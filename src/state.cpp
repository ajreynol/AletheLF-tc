/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "state.h"

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "parser.h"
#include "util/filesystem.h"

namespace ethos {

Options::Options()
{
  d_parseLet = true;
  d_printLet = false;
  d_stats = false;
  d_statsCompact = false;
  d_ruleSymTable = true;
  d_normalizeDecimal = true;
  d_normalizeHexadecimal = true;
  d_normalizeNumeral = false;
  d_binderFresh = false;
}

bool Options::setOption(const std::string& key, bool val)
{
  if (key == "binder-fresh")
  {
    d_binderFresh = val;
  }
  else if (key == "parse-let")
  {
    d_parseLet = val;
  }
  else if (key == "print-let")
  {
    d_printLet = val;
  }
  else if (key == "stats")
  {
    d_stats = val;
  }
  else if (key == "stats-compact")
  {
    if (val)
    {
      // also implies stats are enabled.
      d_stats = val;
    }
    d_statsCompact = val;
  }
  else if (key == "rule-sym-table")
  {
    d_ruleSymTable = val;
  }
  else if (key == "normalize-dec")
  {
    d_normalizeDecimal = val;
  }
  else if (key == "normalize-num")
  {
    d_normalizeNumeral = val;
  }
  else if (key == "normalize-hex")
  {
    d_normalizeHexadecimal = val;
  }
  else
  {
    return false;
  }
  Trace("options") << "setOption(\"" << key << "\", " << val << ")"
                   << std::endl;
  return true;
}

State::State(Options& opts, Stats& stats)
    : d_hashCounter(0),
      d_hasReference(false),
      d_inGarbageCollection(false),
      d_tc(*this, opts),
      d_opts(opts),
      d_stats(stats),
      d_plugin(nullptr)
{
  ExprValue::d_state = this;
  d_absType = Expr(mkExprInternal(Kind::ABSTRACT_TYPE, {}));

  // lambda is not builtin?
  // forall, exists, choice?
  //bindBuiltin("lambda", Kind::LAMBDA, true);
  bindBuiltin("->", Kind::FUNCTION_TYPE);
  bindBuiltin("_", Kind::APPLY);
  bindBuiltin("eo::_", Kind::PARAMETERIZED);

  bindBuiltinEval("is_eq", Kind::EVAL_IS_EQ);
  bindBuiltinEval("ite", Kind::EVAL_IF_THEN_ELSE);
  bindBuiltinEval("requires", Kind::EVAL_REQUIRES);
  bindBuiltinEval("hash", Kind::EVAL_HASH);
  bindBuiltinEval("nameof", Kind::EVAL_NAME_OF);
  bindBuiltinEval("typeof", Kind::EVAL_TYPE_OF);
  bindBuiltinEval("var", Kind::EVAL_VAR);
  bindBuiltinEval("cmp", Kind::EVAL_COMPARE);
  bindBuiltinEval("is_z", Kind::EVAL_IS_Z);
  bindBuiltinEval("is_q", Kind::EVAL_IS_Q);
  bindBuiltinEval("is_bin", Kind::EVAL_IS_BIN);
  bindBuiltinEval("is_str", Kind::EVAL_IS_STR);
  bindBuiltinEval("is_bool", Kind::EVAL_IS_BOOL);
  bindBuiltinEval("is_var", Kind::EVAL_IS_VAR);
  // lists
  bindBuiltinEval("nil", Kind::EVAL_NIL);
  bindBuiltinEval("cons", Kind::EVAL_CONS);
  bindBuiltinEval("list_len", Kind::EVAL_LIST_LENGTH);
  bindBuiltinEval("list_concat", Kind::EVAL_LIST_CONCAT);
  bindBuiltinEval("list_nth", Kind::EVAL_LIST_NTH);
  bindBuiltinEval("list_find", Kind::EVAL_LIST_FIND);
  // boolean
  bindBuiltinEval("not", Kind::EVAL_NOT);
  bindBuiltinEval("and", Kind::EVAL_AND);
  bindBuiltinEval("or", Kind::EVAL_OR);
  bindBuiltinEval("xor", Kind::EVAL_XOR);
  // arithmetic
  bindBuiltinEval("add", Kind::EVAL_ADD);
  bindBuiltinEval("neg", Kind::EVAL_NEG);
  bindBuiltinEval("mul", Kind::EVAL_MUL);
  bindBuiltinEval("zdiv", Kind::EVAL_INT_DIV);
  bindBuiltinEval("zmod", Kind::EVAL_INT_MOD);
  bindBuiltinEval("qdiv", Kind::EVAL_RAT_DIV);
  bindBuiltinEval("is_neg", Kind::EVAL_IS_NEG);
  bindBuiltinEval("to_z", Kind::EVAL_TO_INT);
  bindBuiltinEval("to_q", Kind::EVAL_TO_RAT);
  bindBuiltinEval("to_bin", Kind::EVAL_TO_BIN);
  bindBuiltinEval("to_str", Kind::EVAL_TO_STRING);
  bindBuiltinEval("gt", Kind::EVAL_GT);
  // strings
  bindBuiltinEval("len", Kind::EVAL_LENGTH);
  bindBuiltinEval("concat", Kind::EVAL_CONCAT);
  bindBuiltinEval("extract", Kind::EVAL_EXTRACT);
  bindBuiltinEval("find", Kind::EVAL_FIND);
  // datatypes
  bindBuiltinEval("dt_constructors", Kind::EVAL_DT_CONSTRUCTORS);
  bindBuiltinEval("dt_selectors", Kind::EVAL_DT_SELECTORS);

  // as
  bindBuiltinEval("as", Kind::AS);

  // note we don't allow parsing (Proof ...), (Quote ...), or (quote ...).

  // common constants
  d_type = Expr(mkExprInternal(Kind::TYPE, {}));
  d_boolType = Expr(mkExprInternal(Kind::BOOL_TYPE, {}));
  d_true = Expr(new Literal(true));
  bind("true", d_true);
  d_false = Expr(new Literal(false));
  bind("false", d_false);

  // builtin lists
  d_listType = Expr(mkSymbolInternal(Kind::CONST, "eo::List", d_type));
  bind("eo::List", d_listType);
  d_listNil = Expr(mkSymbolInternal(Kind::CONST, "eo::List::nil", d_listType));
  bind("eo::List::nil", d_listNil);
  Expr t = Expr(mkSymbolInternal(Kind::PARAM, "T", d_type));
  std::vector<Expr> argTypes;
  argTypes.push_back(t);
  argTypes.push_back(d_listType);
  Expr consType = mkFunctionType(argTypes, d_listType);
  d_listCons = Expr(mkSymbolInternal(Kind::CONST, "eo::List::cons", consType));
  bind("eo::List::cons", d_listCons);
  markConstructorKind(d_listCons, Attr::RIGHT_ASSOC_NIL, d_listNil);

  // we do not export eo::null
  // for now, eo::? is (undocumented) syntax for abstract type
  bind("eo::?", d_absType);
  // self is a distinguished parameter
  d_self = Expr(mkSymbolInternal(Kind::PARAM, "eo::self", d_absType));
  bind("eo::self", d_self);
  d_conclusion =
      Expr(mkSymbolInternal(Kind::PARAM, "eo::conclusion", d_boolType));
  // eo::conclusion is not globally bound, since it can only appear
  // in :requires.
}

State::~State() {}

void State::reset()
{
  d_symTable.clear();
  d_assumptions.clear();
  d_assumptionsSizeCtx.clear();
  d_decls.clear();
  d_declsSizeCtx.clear();
  if (d_plugin!=nullptr)
  {
    d_plugin->reset();
  }
}

void State::pushScope()
{
  d_declsSizeCtx.push_back(d_decls.size());
  if (d_plugin!=nullptr)
  {
    d_plugin->pushScope();
  }
}

void State::popScope()
{
  if (d_plugin!=nullptr)
  {
    d_plugin->popScope();
  }
  if (d_declsSizeCtx.empty())
  {
    EO_FATAL() << "State::popScope: empty context";
  }
  size_t lastSize = d_declsSizeCtx.back();
  d_declsSizeCtx.pop_back();
  size_t i = d_decls.size();
  while (i > lastSize)
  {
    i--;
    // Check if overloaded, which is the case if the last overloaded
    // declaration had the same name.
    if (!d_overloadedDecls.empty() && d_overloadedDecls.back()==d_decls[i])
    {
      d_overloadedDecls.pop_back();
      std::map<std::string, Expr>::iterator its = d_symTable.find(d_decls[i]);
      Assert (its!=d_symTable.end());
      // it should be overloaded
      AppInfo* ai = getAppInfo(its->second.getValue());
      Assert (ai!=nullptr);
      // we always have at least 2 overloads
      Assert (ai->d_overloads.size()>=2);
      // was overloaded, we revert the binding
      ai->d_overloads.pop_back();
      Expr tmp = ai->d_overloads.back();
      its->second = tmp;
      continue;
    }
    Trace("overload") << "** unbind " << d_decls[i] << std::endl;
    d_symTable.erase(d_decls[i]);
  }
  d_decls.resize(lastSize);
}

void State::pushAssumptionScope()
{
  // push scope
  pushScope();
  // remember assumption size
  d_assumptionsSizeCtx.push_back(d_assumptions.size());
}

void State::popAssumptionScope()
{
  // process assumptions
  size_t lastSize = d_assumptionsSizeCtx.back();
  d_assumptionsSizeCtx.pop_back();
  d_assumptions.resize(lastSize);
  // pop the parsing scope
  popScope();
}
bool State::includeFile(const std::string& s, bool isSignature)
{
  return includeFile(s, isSignature, false, d_null);
}
bool State::includeFile(const std::string& s, bool isSignature, bool isReference, const Expr& referenceNf)
{
  Filepath inputPath;
  Filepath file(s);
  if (file.isAbsolute())
  {
    inputPath = file;
  }
  else
  {
    inputPath = d_inputFile.parentPath();
    inputPath.append(file);
  }
  inputPath.makeCanonical();

  if (!inputPath.exists())
  {
    return false;
  }

  if (!markIncluded(inputPath))
  {
    return true;
  }
  Assert (!isReference || !d_hasReference);
  d_hasReference = isReference;
  d_referenceNf = referenceNf;
  Filepath currentPath = d_inputFile;
  d_inputFile = inputPath;
  if (d_plugin!=nullptr)
  {
    Assert (!isReference);
    d_plugin->includeFile(inputPath, isReference, referenceNf);
  }
  Trace("state") << "Include " << inputPath << std::endl;
  Assert (getAssumptionLevel()==0);
  Parser p(*this, isSignature, isReference);
  p.setFileInput(inputPath.getRawPath());
  bool parsedCommand;
  do
  {
    parsedCommand = p.parseNextCommand();
  }
  while (parsedCommand);
  d_inputFile = currentPath;
  Trace("state") << "...finished" << std::endl;
  if (getAssumptionLevel()!=0)
  {
    Assert(!d_declsSizeCtx.empty() && d_declsSizeCtx.back() < d_decls.size());
    EO_FATAL() << "Including file " << inputPath.getRawPath()
               << " did not preserve assumption scope. The most recent open "
                  "assumption was "
               << d_decls[d_declsSizeCtx.back()] << ".";
  }
  return true;
}

bool State::markIncluded(const Filepath& s)
{
  std::set<Filepath>::iterator it = d_includes.find(s);
  if (it != d_includes.end())
  {
    return false;
  }
  d_includes.insert(s);
  return true;
}

void State::markDeleted(ExprValue* e)
{
  Assert(e != nullptr);
  d_stats.d_deleteExprCount++;
  if (d_inGarbageCollection)
  {
    d_toDelete.push_back(e);
    return;
  }
  d_inGarbageCollection = true;
  do
  {
    Kind k = e->getKind();
    Trace("gc") << "Delete " << e << " " << k << std::endl;
    switch(k)
    {
      case Kind::NUMERAL:
      {
        std::unordered_map<Integer, Expr, IntegerHashFunction>::iterator it = d_litIntMap.find(e->asLiteral()->d_int);
        Assert (it!=d_litIntMap.end());
        d_litIntMap.erase(it);
      }
        break;
      case Kind::DECIMAL:
      case Kind::RATIONAL:
      {
        size_t i = k==Kind::DECIMAL ? 0 : 1;
        std::unordered_map<Rational, Expr, RationalHashFunction>& m = d_litRatMap[i];
        std::unordered_map<Rational, Expr, RationalHashFunction>::iterator it = m.find(e->asLiteral()->d_rat);
        Assert (it!=m.end());
        m.erase(it);
      }
        break;
      case Kind::HEXADECIMAL:
      case Kind::BINARY:
      {
        size_t i = k==Kind::HEXADECIMAL ? 0 : 1;
        std::unordered_map<BitVector, Expr, BitVectorHashFunction>& m = d_litBvMap[i];
        std::unordered_map<BitVector, Expr, BitVectorHashFunction>::iterator it = m.find(e->asLiteral()->d_bv);
        Assert (it!=m.end());
        m.erase(it);
      }
        break;
      case Kind::STRING:
      {
        std::unordered_map<String, Expr, StringHashFunction>::iterator it = d_litStrMap.find(e->asLiteral()->d_str);
        Assert (it!=d_litStrMap.end());
        d_litStrMap.erase(it);
      }
        break;
      default:
      {
        if (isSymbol(k))
        {
          std::map<const ExprValue*, AppInfo>::const_iterator it = d_appData.find(e);
          if (it != d_appData.end())
          {
            d_appData.erase(it);
          }
        }
      }
      break;
    }
    std::map<const ExprValue*, size_t>::const_iterator ith = d_hashMap.find(e);
    if (ith != d_hashMap.end())
    {
      d_hashMap.erase(ith);
    }
    std::map<const ExprValue*, Expr>::const_iterator itt = d_typeCache.find(e);
    if (itt != d_typeCache.end())
    {
      d_typeCache.erase(itt);
    }
    // remove from the expression trie
    ExprTrie* et = &d_trie[e->getKind()];
    Assert(et != nullptr);
    const std::vector<ExprValue*>& children = e->d_children;
    et->remove(children);
    // now, free the expression
    free(e);
    if (!d_toDelete.empty())
    {
      e = d_toDelete.back();
      d_toDelete.pop_back();
    }
    else
    {
      e = nullptr;
    }
  } while (e != nullptr);
  d_inGarbageCollection = false;
}

bool State::addAssumption(const Expr& a)
{
  d_assumptions.push_back(a);
  if (d_hasReference)
  {
    // only care if at assumption level zero
    if (d_assumptionsSizeCtx.empty())
    {
      Expr aa = a;
      if (!d_referenceNf.isNull())
      {
        aa = mkExpr(Kind::APPLY, {d_referenceNf, a});
      }
      return d_referenceAsserts.find(aa.getValue()) != d_referenceAsserts.end();
    }
  }
  return true;
}

void State::addReferenceAssert(const Expr& a)
{
  Expr aa = a;
  if (!d_referenceNf.isNull())
  {
    aa = mkExpr(Kind::APPLY, {d_referenceNf, a});
  }
  d_referenceAsserts.insert(aa.getValue());
  // ensure ref count
  d_referenceAssertList.push_back(aa);
}

void State::setLiteralTypeRule(Kind k, const Expr& t)
{
  d_tc.setLiteralTypeRule(k, t);
  if (d_plugin!=nullptr)
  {
    d_plugin->setLiteralTypeRule(k, t);
  }
}

Expr State::mkType()
{
  return d_type;
}

Expr State::mkTypeConstant(const std::string& name, size_t arity)
{
  Expr t;
  if (arity == 0)
  {
    t = d_type;
  }
  else
  {
    std::vector<Expr> args;
    for (size_t i=0; i<arity; i++)
    {
      args.push_back(d_type);
    }
    t = mkFunctionType(args, d_type);
  }
  return mkSymbol(Kind::CONST, name, t);
}

Expr State::mkFunctionType(const std::vector<Expr>& args, const Expr& ret, bool flatten)
{
  if (args.empty())
  {
    return ret;
  }
  // process restrictions
  if (!flatten)
  {
    std::vector<ExprValue*> atypes;
    for (size_t i = 0, nargs = args.size(); i < nargs; i++)
    {
      atypes.push_back(args[i].getValue());
    }
    atypes.push_back(ret.getValue());
    return Expr(mkExprInternal(Kind::FUNCTION_TYPE, atypes));
  }
  Expr curr = ret;
  for (size_t i=0, nargs = args.size(); i<nargs; i++)
  {
    Expr a = args[(nargs-1)-i];
    // process arguments
    if (a.getKind() == Kind::EVAL_REQUIRES)
    {
      curr = mkRequires(a[0], a[1], curr);
      a = a[2];
    }
    // append the function
    curr = Expr(
        mkExprInternal(Kind::FUNCTION_TYPE, {a.getValue(), curr.getValue()}));
  }
  return curr;
}

Expr State::mkRequires(const std::vector<Expr>& args, const Expr& ret)
{
  Expr curr = ret;
  for (size_t i=0, nargs=args.size(); i<nargs; i++)
  {
    size_t ii = (nargs-1)-i;
    Assert(args[ii].getKind() == Kind::TUPLE && args[ii].getNumChildren() == 2);
    curr = mkRequires(args[ii][0], args[ii][1], curr);
  }
  return curr;
}

Expr State::mkRequires(const Expr& a1, const Expr& a2, const Expr& ret)
{
  if (a1==a2)
  {
    // trivially equal to return
    return ret;
  }
  return Expr(mkExprInternal(Kind::EVAL_REQUIRES,
                             {a1.getValue(), a2.getValue(), ret.getValue()}));
}

Expr State::mkAbstractType() { return d_absType; }

Expr State::mkBoolType()
{
  return d_boolType;
}

Expr State::mkListType() { return d_listType; }

Expr State::mkProofType(const Expr& proven)
{
  return Expr(mkExprInternal(Kind::PROOF_TYPE, {proven.getValue()}));
}
Expr State::mkQuoteType(const Expr& t)
{
  return Expr(mkExprInternal(Kind::QUOTE_TYPE, {t.getValue()}));
}

Expr State::mkBuiltinType(Kind k)
{
  // for now, just use abstract type
  return d_absType;
}

Expr State::mkSymbol(Kind k, const std::string& name, const Expr& type)
{
  return Expr(mkSymbolInternal(k, name, type));
}

Expr State::mkSelf()
{
  return d_self;
}

Expr State::mkConclusion()
{
  return d_conclusion;
}

Expr State::mkPair(const Expr& t1, const Expr& t2)
{
  return Expr(mkExprInternal(Kind::TUPLE, {t1.getValue(), t2.getValue()}));
}

ExprValue* State::mkSymbolInternal(Kind k,
                                   const std::string& name,
                                   const Expr& type)
{
  d_stats.d_mkExprCount++;
  // TODO: symbols can be shared if no attributes
  /*
  std::tuple<Kind, std::string, Expr> key(k, name, type);  
  std::map<std::tuple<Kind, std::string, Expr>, Expr>::iterator it = d_symcMap.find(key);
  if (it!=d_symcMap.end())
  {
    return it->second;
  }
  */
  d_stats.d_symCount++;
  d_stats.d_exprCount++;
  std::vector<ExprValue*> emptyVec;
  ExprValue* v = new Literal(k, name);
  // immediately set its type
  d_typeCache[v] = type;
  Trace("type_checker") << "TYPE " << name << " : " << type << std::endl;
  //d_symcMap[key] = v;
  return v;
}

Expr State::mkExpr(Kind k, const std::vector<Expr>& children)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  if (k==Kind::APPLY)
  {
    Assert(!children.empty());
    // see if there is a special way of building terms for the head
    ExprValue* hd = vchildren[0];
    // immediately strip off PARAMETERIZED if it exists
    hd = hd->getKind()==Kind::PARAMETERIZED ? (*hd)[1] : hd;
    AppInfo* ai = getAppInfo(hd);
    if (ai!=nullptr)
    {
      if (ai->d_kind!=Kind::NONE)
      {
        Trace("state-debug") << "Process builtin app " << ai->d_kind << std::endl;
        if (ai->d_kind==Kind::FUNCTION_TYPE)
        {
          // functions (from parsing) are flattened here
          std::vector<Expr> achildren(children.begin()+1, children.end()-1);
          return mkFunctionType(achildren, children.back());
        }
        else if (ai->d_kind==Kind::PARAMETERIZED)
        {
          // make as tuple
          std::vector<Expr> achildren(vchildren.begin()+2, vchildren.end());
          return mkParameterized(vchildren[1], achildren);
        }
        // another builtin operator, possibly APPLY
        std::vector<Expr> achildren(children.begin()+1, children.end());
        // must call mkExpr again, since we may auto-evaluate
        return mkExpr(ai->d_kind, achildren);
      }
      if (!ai->d_overloads.empty())
      {
        Trace("overload") << "Use overload when constructing " << k << " " << children << std::endl;
        Expr ret = getOverloadInternal(ai->d_overloads, children);
        if (!ret.isNull())
        {
          vchildren[0] = ret.getValue();
          Trace("overload") << "...found overload " << ret << std::endl;
          return vchildren.size()<=2 ? Expr(mkExprInternal(k, vchildren)) : Expr(mkApplyInternal(vchildren));
        }
        Warning() << "No overload found when constructing application "
                  << children << std::endl;
      }
      Trace("state-debug") << "Process category " << ai->d_attrCons << " for " << children[0] << std::endl;
      size_t nchild = vchildren.size();
      // Compute the "constructor term" for the operator, which may involve
      // type inference. We store the constructor term in consTerm and operator
      // in hdTerm, where notice hdTerm is of kind PARAMETERIZED if consTerm
      // (prior to resolution) was PARAMETERIZED. So, for example, applying
      // `bvor` to `a` of type `(BitVec 4)` results in
      //   hdTerm := (PARAMETERIZED (4) bvor),
      //   consTerm := #b0000.
      Expr hdTerm;
      Expr consTerm;
      d_tc.computedParameterizedInternal(ai, children, hdTerm, consTerm);
      Trace("state-debug") << "...updated " << hdTerm << " / " << consTerm << std::endl;
      vchildren[0] = hd;
      // if it has a constructor attribute
      switch (ai->d_attrCons)
      {
        case Attr::LEFT_ASSOC:
        case Attr::RIGHT_ASSOC:
        case Attr::LEFT_ASSOC_NIL:
        case Attr::RIGHT_ASSOC_NIL:
        {
          // This means that we don't construct bogus terms when e.g.
          // right-assoc-nil operators are used in side condition bodies.
          // note that nchild>=2 treats e.g. (or a) as (or a false).
          // checking nchild>2 treats (or a) as a function Bool -> Bool.
          if (nchild>=2)
          {
            bool isLeft = (ai->d_attrCons==Attr::LEFT_ASSOC ||
                           ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            bool isNil = (ai->d_attrCons==Attr::RIGHT_ASSOC_NIL ||
                          ai->d_attrCons==Attr::LEFT_ASSOC_NIL);
            size_t i = 1;
            ExprValue* curr = vchildren[isLeft ? i : nchild - i];
            std::vector<ExprValue*> cc{hd, nullptr, nullptr};
            size_t nextIndex = isLeft ? 2 : 1;
            size_t prevIndex = isLeft ? 1 : 2;
            if (isNil)
            {
              if (getConstructorKind(curr) != Attr::LIST)
              {
                // if the last term is not marked as a list variable and
                // we have a null terminator, then we insert the null terminator
                Trace("state-debug") << "...insert nil terminator " << consTerm << std::endl;
                if (consTerm.isNull())
                {
                  // if we failed to infer a nil terminator (likely due to
                  // a non-ground parameter), then we insert a placeholder
                  // (eo::nil f t1 ... tn), which if t1...tn are non-ground
                  // will evaluate to the proper nil terminator when
                  // instantiated.
                  curr = mkExprInternal(Kind::EVAL_NIL, vchildren);
                }
                else
                {
                  curr = consTerm.getValue();
                }
                i--;
              }
            }
            // now, add the remaining children
            i++;
            while (i<nchild)
            {
              cc[prevIndex] = curr;
              cc[nextIndex] = vchildren[isLeft ? i : nchild - i];
              // if the "head" child is marked as list, we construct Kind::EVAL_LIST_CONCAT
              if (isNil && getConstructorKind(cc[nextIndex]) == Attr::LIST)
              {
                curr = mkExprInternal(Kind::EVAL_LIST_CONCAT, cc);
              }
              else
              {
                curr = mkApplyInternal(cc);
              }
              i++;
            }
            Trace("type_checker") << "...return for " << children[0] << std::endl;
            return Expr(curr);
          }
          // otherwise partial??
        }
          break;
        case Attr::CHAINABLE:
        {
          std::vector<Expr> cchildren;
          Assert(!consTerm.isNull());
          cchildren.push_back(consTerm);
          std::vector<ExprValue*> cc{hd, nullptr, nullptr};
          for (size_t i=1, nchild = vchildren.size()-1; i<nchild; i++)
          {
            cc[1] = vchildren[i];
            cc[2] = vchildren[i + 1];
            cchildren.emplace_back(mkApplyInternal(cc));
          }
          if (cchildren.size()==2)
          {
            // no need to chain
            return cchildren[1];
          }
          // note this could loop
          return mkExpr(Kind::APPLY, cchildren);
        }
          break;
        case Attr::PAIRWISE:
        {
          std::vector<Expr> cchildren;
          Assert(!consTerm.isNull());
          cchildren.push_back(consTerm);
          std::vector<ExprValue*> cc{hd, nullptr, nullptr};
          for (size_t i=1, nchild = vchildren.size(); i<nchild-1; i++)
          {
            for (size_t j=i+1; j<nchild; j++)
            {
              cc[1] = vchildren[i];
              cc[2] = vchildren[j];
              cchildren.emplace_back(mkApplyInternal(cc));
            }
          }
          if (cchildren.size()==2)
          {
            // no need to chain
            return cchildren[1];
          }
          // note this could loop
          return mkExpr(Kind::APPLY, cchildren);
        }
          break;
        case Attr::OPAQUE:
        {
          // determine how many opaque children
          Expr hdt = Expr(hd);
          const Expr& t = d_tc.getType(hdt);
          Assert (t.getKind()==Kind::FUNCTION_TYPE);
          size_t nargs = t.getNumChildren()-1;
          if (nargs>=children.size())
          {
            Warning() << "Too few arguments when applying opaque symbol " << hdt << std::endl;
          }
          else
          {
            std::vector<Expr> ochildren(children.begin(), children.begin()+1+nargs);
            Expr op = mkExpr(Kind::APPLY_OPAQUE, ochildren);
            Trace("opaque") << "Construct opaque operator " << op << std::endl;
            if (nargs+1==children.size())
            {
              Trace("opaque") << "...return operator" << std::endl;
              return op;
            }
            // higher order
            std::vector<Expr> rchildren;
            rchildren.push_back(op);
            rchildren.insert(rchildren.end(), children.begin()+1+nargs, children.end());
            Trace("opaque") << "...return operator applied to children" << std::endl;
            return mkExpr(Kind::APPLY, rchildren);
          }
        }
        default:
          break;
      }
    }
    Kind hk = hd->getKind();
    if (hk==Kind::LAMBDA)
    {
      // beta-reduce eagerly, if the correct arity
      const std::vector<ExprValue*>& vars = (*hd)[0]->getChildren();
      size_t nvars = vars.size();
      if (nvars==children.size()-1)
      {
        Ctx ctx;
        for (size_t i=0; i<nvars; i++)
        {
          ctx[vars[i]] = vchildren[i + 1];
        }
        Expr ret = d_tc.evaluate((*hd)[1], ctx);
        Trace("state") << "BETA_REDUCE " << Expr((*hd)[1]) << " " << ctx << " = " << ret << std::endl;
        return ret;
      }
      else
      {
        Warning() << "Wrong number of arguments when applying " << Expr(hd) << std::endl;
      }
    }
    else if (hk==Kind::PROGRAM_CONST || hk==Kind::ORACLE)
    {
      // have to check whether we have marked the constructor kind, which is
      // not the case i.e. if we are constructing applications corresponding to
      // the cases in the program definition itself.
      if (getConstructorKind(hd)!=Attr::NONE)
      {
        Expr hdt = Expr(hd);
        const Expr& t = d_tc.getType(hdt);
        // only do this if the correct arity
        if (t.getNumChildren() == children.size())
        {
          Ctx ctx;
          Expr e = d_tc.evaluateProgramInternal(vchildren, ctx);
          if (!e.isNull())
          {
            Expr ret = d_tc.evaluate(e.getValue(), ctx);
            Trace("state") << "EAGER_EVALUATE " << ret << std::endl;
            return ret;
          }
        }
        else
        {
          Warning() << "Wrong number of arguments when applying program " << Expr(hd)
                    << ", " << t.getNumChildren() << " arguments expected, got "
                    << children.size() << std::endl;
        }
      }
    }
    // Most functions are unary and require currying if applied to more than one argument.
    // The exceptions to this are operators whose types are not flattened (programs and proof rules).
    if (children.size()>2)
    {
      if (hk!=Kind::PROGRAM_CONST && hk!=Kind::PROOF_RULE && hk!=Kind::ORACLE)
      {
        // return the curried version
        return Expr(mkApplyInternal(vchildren));
      }
    }
  }
  else if (isLiteralOp(k))
  {
    // only if correct arity, else we will catch the type error
    bool isArityOk = TypeChecker::checkArity(k, vchildren.size());
    if (isArityOk)
    {
      // return the evaluation
      return d_tc.evaluateLiteralOp(k, vchildren);
    }
    else
    {
      Warning() << "Wrong number of arguments when applying literal op " << k
                << ", " << children.size() << " arguments" << std::endl;
    }
  }
  else if (k==Kind::AS)
  {
    // if it has 2 children, process it, otherwise we make the bogus term
    // below
    if (vchildren.size()==2)
    {
      Trace("overload") << "process eo::as " << children[0] << " " << children[1] << std::endl;
      AppInfo* ai = getAppInfo(vchildren[0]);
      Expr ret = children[0];
      std::pair<std::vector<Expr>, Expr> ftype = children[1].getFunctionType();
      Expr reto;
      // look up the overload
      std::vector<Expr> dummyChildren;
      dummyChildren.push_back(children[1]);
      for (const Expr& t : ftype.first)
      {
        dummyChildren.emplace_back(mkSymbol(Kind::CONST, "tmp", t));
      }
      if (ai!=nullptr && !ai->d_overloads.empty())
      {
        Trace("overload") << "...overloaded" << std::endl;
        reto = getOverloadInternal(ai->d_overloads, dummyChildren, ftype.second.getValue());
      }
      else
      {
        Trace("overload") << "...not overloaded" << std::endl;
        reto = getOverloadInternal({children[0]}, dummyChildren, ftype.second.getValue());
      }
      if (!reto.isNull())
      {
        Trace("overload") << "...found overload " << reto << " " << d_tc.getType(reto) << std::endl;
        return reto;
      }
    }
  }
  return Expr(mkExprInternal(k, vchildren));
}

Expr State::mkTrue()
{
  return d_true;
}

Expr State::mkFalse()
{
  return d_false;
}

Expr State::mkLiteral(Kind k, const std::string& s)
{
  // convert string to literal
  Literal lit;
  switch (k)
  {
    case Kind::BOOLEAN:
      Assert (s=="true" || s=="false");
      return s=="true" ? d_true : d_false;
      break;
    case Kind::NUMERAL: lit = Literal(Integer(s)); break;
    case Kind::DECIMAL: lit = Literal(k, Rational::fromDecimal(s)); break;
    case Kind::RATIONAL: lit = Literal(k, Rational(s)); break;
    case Kind::HEXADECIMAL: lit = Literal(k, BitVector(s, 16)); break;
    case Kind::BINARY: lit = Literal(k, BitVector(s, 2)); break;
    case Kind::STRING: lit = Literal(String(s, true)); break;
    default:
      EO_FATAL() << "Unknown kind for mkLiteral " << k;
      break;
  }
  return Expr(mkLiteralInternal(lit));
}

Expr State::mkParameterized(const ExprValue* hd, const std::vector<Expr>& params)
{
  return mkExpr(Kind::PARAMETERIZED, {mkExpr(Kind::TUPLE, params), Expr(hd)});
}

Expr State::mkList(const std::vector<Expr>& args)
{
  if (args.empty())
  {
    return d_listNil;
  }
  std::vector<Expr> largs;
  largs.push_back(d_listCons);
  largs.insert(largs.end(), args.begin(), args.end());
  return mkExpr(Kind::APPLY, largs);
}

ExprValue* State::mkLiteralInternal(Literal& l)
{
  d_stats.d_mkExprCount++;
  ExprValue * ev;
  Kind k = l.getKind();
  switch (k)
  {
    case Kind::BOOLEAN:
      return l.d_bool ? d_true.getValue() : d_false.getValue();
    case Kind::NUMERAL:
    {
      std::unordered_map<Integer, Expr, IntegerHashFunction>::iterator it = d_litIntMap.find(l.d_int);
      if (it!=d_litIntMap.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(l.d_int);
      d_litIntMap[l.d_int] = Expr(ev);
    }
      break;
    case Kind::DECIMAL:
    case Kind::RATIONAL:
    {
      size_t i = k==Kind::DECIMAL ? 0 : 1;
      std::unordered_map<Rational, Expr, RationalHashFunction>& m = d_litRatMap[i];
      std::unordered_map<Rational, Expr, RationalHashFunction>::iterator it = m.find(l.d_rat);
      if (it!=m.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(k, l.d_rat);
      m[l.d_rat] = Expr(ev);
    }
      break;
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    {
      size_t i = k==Kind::HEXADECIMAL ? 0 : 1;
      std::unordered_map<BitVector, Expr, BitVectorHashFunction>& m = d_litBvMap[i];
      std::unordered_map<BitVector, Expr, BitVectorHashFunction>::iterator it = m.find(l.d_bv);
      if (it!=m.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(k, l.d_bv);
      m[l.d_bv] = Expr(ev);
    }
      break;
    case Kind::STRING:
    {
      std::unordered_map<String, Expr, StringHashFunction>::iterator it = d_litStrMap.find(l.d_str);
      if (it!=d_litStrMap.end())
      {
        return it->second.getValue();
      }
      ev = new Literal(l.d_str);
      d_litStrMap[l.d_str] = Expr(ev);
    }
      break;
    default:
      EO_FATAL() << "Unknown kind for mkLiteralInternal " << l.getKind();
      break;
  }
  d_stats.d_litCount++;
  d_stats.d_exprCount++;
  return ev;
}

ExprValue* State::mkApplyInternal(const std::vector<ExprValue*>& children)
{
  Assert(children.size() > 2);
  // requires currying
  ExprValue* curr = children[0];
  for (size_t i=1, nchildren = children.size(); i<nchildren; i++)
  {
    curr = mkExprInternal(Kind::APPLY, {curr, children[i]});
  }
  return curr;
}

ExprValue* State::mkExprInternal(Kind k,
                                 const std::vector<ExprValue*>& children)
{
  d_stats.d_mkExprCount++;
  ExprTrie* et = &d_trie[k];
  et = et->get(children);
  if (et->d_data!=nullptr)
  {
    return et->d_data;
  }
  d_stats.d_exprCount++;
  ExprValue* ev = new ExprValue(k, children);
  Trace("gc") << "New " << ev << " " << k << std::endl;
  et->d_data = ev;
  return ev;
}

bool State::bind(const std::string& name, const Expr& e)
{
  // compiler is agnostic to which symbol table, record it here
  if (d_plugin!=nullptr)
  {
    d_plugin->bind(name, e);
  }
  // if using a separate symbol table for rules
  if (d_opts.d_ruleSymTable && e.getKind() == Kind::PROOF_RULE)
  {
    // don't bind at non-global scope
    Assert (d_declsSizeCtx.empty());
    if (d_ruleSymTable.find(name)!=d_ruleSymTable.end())
    {
      return false;
    }
    d_ruleSymTable[name] = e;
    return true;
  }
  // otherwise use the main symbol table
  std::map<std::string, Expr>::iterator its = d_symTable.find(name);
  if (its!=d_symTable.end())
  {
    Trace("overload") << "** overload: " << name << std::endl;
    // if already bound, we overload
    AppInfo& ai = d_appData[its->second.getValue()];
    std::vector<Expr>& ov = ai.d_overloads;
    AppInfo& ain = d_appData[e.getValue()];
    std::vector<Expr>& ovn = ain.d_overloads;
    if (ov.empty())
    {
      // if first time overloading, add the original symbol
      ovn.emplace_back(its->second);
    }
    else
    {
      // Otherwise, carry all of the overloads from the previous symbol.
      // Note that since we carry the overloads for each symbol, the space
      // required here is quadratic, but the number of overloads per symbol
      // should be very small.
      ovn.insert(ovn.end(), ov.begin(), ov.end());
    }
    ovn.emplace_back(e);
    // add to declaration
    if (!d_declsSizeCtx.empty())
    {
      d_overloadedDecls.emplace_back(name);
    }
  }
  // Trace("state-debug") << "bind " << name << " -> " << &e << std::endl;
  d_symTable[name] = e;
  // only have to remember if not at global scope
  if (!d_declsSizeCtx.empty())
  {
    d_decls.emplace_back(name);
  }
  return true;
}

Expr State::mkBinderList(const ExprValue* ev, const std::vector<Expr>& vs)
{
  Assert (!vs.empty());
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(ev);
  Assert (it!=d_appData.end());
  std::vector<Expr> vlist;
  vlist.push_back(it->second.d_attrConsTerm);
  vlist.insert(vlist.end(), vs.begin(), vs.end());
  return mkExpr(Kind::APPLY, vlist);
}

Expr State::mkLetBinderList(const ExprValue* ev, const std::vector<std::pair<Expr, Expr>>& lls)
{
  Assert (!lls.empty());
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(ev);
  Assert (it!=d_appData.end());
  Expr cons = it->second.d_attrConsTerm;
  Assert (cons.getKind()==Kind::TUPLE && cons.getNumChildren()==2);
  Expr pairCons = cons[0];
  Expr listCons = cons[1];
  std::vector<Expr> vs;
  for (const std::pair<Expr, Expr>& ll : lls)
  {
    vs.emplace_back(mkExpr(Kind::APPLY, {pairCons, ll.first, ll.second}));
  }
  std::vector<Expr> vlist;
  vlist.push_back(listCons);
  vlist.insert(vlist.end(), vs.begin(), vs.end());
  return mkExpr(Kind::APPLY, vlist);
}

const ExprValue* State::getBaseOperator(const ExprValue * v) const
{
  if (v->getKind()==Kind::PARAMETERIZED)
  {
    return (*v)[0];
  }
  return v;
}

Attr State::getConstructorKind(const ExprValue* v) const
{
  const AppInfo* ai = getAppInfo(v);
  if (ai!=nullptr)
  {
    return ai->d_attrCons;
  }
  return Attr::NONE;
}


Expr State::getVar(const std::string& name) const
{
  std::map<std::string, Expr>::const_iterator it = d_symTable.find(name);
  if (it!=d_symTable.end())
  {
    return it->second;
  }
  return d_null;
}

Expr State::getBoundVar(const std::string& name, const Expr& type)
{
  std::pair<std::string, const ExprValue*> key(name, type.getValue());
  std::map<std::pair<std::string, const ExprValue*>, Expr>::iterator it = d_boundVars.find(key);
  if (it!=d_boundVars.end())
  {
    return it->second;
  }
  Expr ret = mkSymbol(Kind::VARIABLE, name, type);
  d_boundVars[key] = ret;
  return ret;
}

Expr State::getProofRule(const std::string& name) const
{
  const std::map<std::string, Expr>& t = d_opts.d_ruleSymTable ? d_ruleSymTable : d_symTable;
  std::map<std::string, Expr>::const_iterator it = t.find(name);
  if (it!=t.end())
  {
    return it->second;
  }
  return d_null;
}

bool State::getActualPremises(const ExprValue* rule,
                              std::vector<Expr>& given,
                              std::vector<Expr>& actual)
{
  AppInfo* ainfo = getAppInfo(rule);
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::PREMISE_LIST)
  {
    Expr plCons = ainfo->d_attrConsTerm;
    if (!plCons.isNull())
    {
      std::vector<Expr> achildren;
      achildren.push_back(plCons);
      for (Expr& e : given)
      {
        // should be proof types
        Expr eproven = d_tc.getType(e);
        if (eproven.isNull() || eproven.getKind() != Kind::PROOF_TYPE)
        {
          return false;
        }
        achildren.push_back(eproven[0]);
      }
      Expr ap;
      if (achildren.size()==1)
      {
        // the nil terminator if applied to empty list
        AppInfo* aic = getAppInfo(plCons.getValue());
        Attr ck = aic->d_attrCons;
        if (ck==Attr::RIGHT_ASSOC_NIL || ck==Attr::LEFT_ASSOC_NIL)
        {
          ap = aic->d_attrConsTerm;
        }
        else
        {
          return false;
        }
      }
      else
      {
        ap = mkExpr(Kind::APPLY, achildren);
      }
      Expr pfap = mkProofType(ap);
      // TODO: collect operator???
      // dummy, const term of the given proof type
      Expr n = mkSymbol(Kind::CONST, "tmp", pfap);
      actual.push_back(n);
      return true;
    }
  }
  actual = given;
  return true;
}

Expr State::getProgram(const ExprValue* ev)
{
  AppInfo* ainfo = getAppInfo(ev);
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::PROGRAM)
  {
    return ainfo->d_attrConsTerm;
  }
  return d_null;
}
bool State::getOracleCmd(const ExprValue* oracle, std::string& ocmd)
{
  AppInfo* ainfo = getAppInfo(oracle);
  if (ainfo!=nullptr && ainfo->d_attrCons==Attr::ORACLE)
  {
    Expr oexpr = ainfo->d_attrConsTerm;
    Assert(!oexpr.isNull());
    ocmd = oexpr.getSymbol();
    return true;
  }
  return false;
}

size_t State::getAssumptionLevel() const
{
  return d_assumptionsSizeCtx.size();
}

std::vector<Expr> State::getCurrentAssumptions() const
{
  size_t start = d_assumptionsSizeCtx.empty() ? 0 : d_assumptionsSizeCtx.back();
  std::vector<Expr> as(d_assumptions.begin()+start, d_assumptions.end());
  return as;
}

size_t State::getHash(const ExprValue* e)
{
  std::map<const ExprValue*, size_t>::const_iterator it = d_hashMap.find(e);
  if (it!=d_hashMap.end())
  {
    return it->second;
  }
  d_hashCounter++;
  size_t ret = d_hashCounter;
  d_hashMap[e] = ret;
  return ret;
}

bool State::hasReference() const
{
  return d_hasReference;
}

void State::markProofRuleSorry(const ExprValue * e)
{
  d_pfrSorry.insert(e);
}

bool State::isProofRuleSorry(const ExprValue* e) const
{
  return d_pfrSorry.find(e)!=d_pfrSorry.end();
}

AppInfo* State::getAppInfo(const ExprValue* e)
{
  Assert (e->getKind()!=Kind::PARAMETERIZED);
  std::map<const ExprValue *, AppInfo>::iterator it = d_appData.find(e);
  if (it!=d_appData.end())
  {
    return &it->second;
  }
  return nullptr;
}

const AppInfo* State::getAppInfo(const ExprValue* e) const
{
  Assert (e->getKind()!=Kind::PARAMETERIZED);
  std::map<const ExprValue *, AppInfo>::const_iterator it = d_appData.find(e);
  if (it!=d_appData.end())
  {
    return &it->second;
  }
  return nullptr;
}

ExprValue* State::lookupType(const ExprValue* e) const
{
  std::map<const ExprValue*, Expr>::const_iterator itt = d_typeCache.find(e);
  if (itt != d_typeCache.end())
  {
    return itt->second.getValue();
  }
  return nullptr;
}

TypeChecker& State::getTypeChecker()
{
  return d_tc;
}

Options& State::getOptions()
{
  return d_opts;
}

Stats& State::getStats()
{
  return d_stats;
}

void State::setPlugin(Plugin* p)
{
  Assert (p!=nullptr);
  d_plugin = p;
  d_tc.d_plugin = p;
  // call the initialize method of the plugin
  d_plugin->initialize();
}

Plugin* State::getPlugin()
{
  return d_plugin;
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac)
{
  // type is irrelevant, assign abstract
  bindBuiltin(name, k, ac, d_absType);
}

void State::bindBuiltin(const std::string& name, Kind k, Attr ac, const Expr& t)
{
  Expr c = mkSymbol(Kind::CONST, name, t);
  bind(name, c);
  if (ac!=Attr::NONE || k!=Kind::NONE)
  {
    // associate the information
    AppInfo& ai = d_appData[c.getValue()];
    ai.d_kind = k;
    ai.d_attrCons = ac;
  }
}

void State::bindBuiltinEval(const std::string& name, Kind k, Attr ac)
{
  bindBuiltin("eo::"+name, k, ac);
}

void State::defineProgram(const Expr& v, const Expr& prog)
{
  markConstructorKind(v, Attr::PROGRAM, prog);
  if (d_plugin!=nullptr)
  {
    d_plugin->defineProgram(v, prog);
  }
}

bool State::markConstructorKind(const Expr& v, Attr a, const Expr& cons)
{
  Expr acons = cons;
  if (a==Attr::ORACLE)
  {
    // use full path
    std::string ocmd = cons.getSymbol();

    Filepath inputPath = d_inputFile.parentPath();
    inputPath.append(Filepath(ocmd));
    inputPath.makeCanonical();

    if (!inputPath.exists())
    {
      Warning() << "State:: could not include \"" + ocmd + "\" for oracle definition";
      return false;
    }

    acons = mkLiteral(Kind::STRING, inputPath.getRawPath());
  }
  Assert (isSymbol(v.getKind()));
  AppInfo& ai = d_appData[v.getValue()];
  Assert (ai.d_attrCons==Attr::NONE);
  ai.d_attrCons = a;
  ai.d_attrConsTerm = acons;
  if (d_plugin!=nullptr)
  {
    d_plugin->markConstructorKind(v, a, acons);
  }
  return true;
}

Expr State::getOverloadInternal(const std::vector<Expr>& overloads,
                                const std::vector<Expr>& children,
                                const ExprValue* retType)
{
  Assert (!overloads.empty());
  Trace("overload") << "Get overload" << std::endl;
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  // try overloads in order until one is found
  Expr tmp;
  for (size_t i=0, noverloads = overloads.size(); i<noverloads; i++)
  {
    // search in reverse order, i.e. the last bound symbol takes precendence
    size_t ii = (noverloads-1)-i;
    vchildren[0] = overloads[ii].getValue();
    // The syntax e.g. (eo::as nil (List Int)) has a different behavior.
    // it does not distinguish a symbol but instead annotates the constructor
    // symbol. This is done as an *opaque* argument to ensure type annotations
    // are not in ordinary positions.
    if (getConstructorKind(vchildren[0]) == Attr::AMB_DATAYPE_CONSTRUCTOR)
    {
      Trace("overload") << "...type arg for ambiguous constructor" << std::endl;
      Expr cons(vchildren[0]);
      Expr rt(retType);
      tmp = mkExpr(Kind::APPLY_OPAQUE, {cons, rt});
      vchildren[0] = tmp.getValue();
    }
    Expr x = vchildren.size() == 1
                 ? Expr(vchildren[0])
                 : (Expr(vchildren.size() > 2
                             ? mkApplyInternal(vchildren)
                             : mkExprInternal(Kind::APPLY, vchildren)));
    Trace("overload") << "...check type of " << x << std::endl;
    Expr t = d_tc.getType(x);
    Trace("overload") << "...has type " << t << std::endl;
    // if term is well-formed, and matches the return type if it exists
    if (!t.isNull() && (retType==nullptr || retType==t.getValue()))
    {
      // return the operator, do not check the remainder
      return Expr(vchildren[0]);
    }
  }
  // otherwise, none found, return null
  return d_null;
}

}  // namespace ethos
