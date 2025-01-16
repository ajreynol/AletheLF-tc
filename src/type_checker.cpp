/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "type_checker.h"

#include <iostream>
#include <set>
#include <unordered_map>

#include "base/check.h"
#include "base/output.h"
#ifdef EO_ORACLES
#include "base/run.h"
#endif /* EO_ORACLES */
#include "expr.h"
#include "literal.h"
#include "parser.h"
#include "state.h"

namespace ethos {

TypeChecker::TypeChecker(State& s, Options& opts) : d_state(s), d_plugin(nullptr)
{
  std::set<Kind> literalKinds = { Kind::BOOLEAN, Kind::NUMERAL, Kind::RATIONAL, Kind::BINARY, Kind::STRING, Kind::DECIMAL, Kind::HEXADECIMAL };
  // initialize literal kinds 
  for (Kind k : literalKinds)
  {
    d_literalTypeRules[k] = d_null;
  }
}

TypeChecker::~TypeChecker()
{
}

void TypeChecker::setLiteralTypeRule(Kind k, const Expr& t)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k;
  }
  else if (!it->second.isNull() && it->second != t)
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k << " to " << t << ", since its type was already set to "
                 << it->second;
  }
  it->second = t;
}

ExprValue* TypeChecker::getOrSetLiteralTypeRule(Kind k)
{
  std::map<Kind, Expr>::iterator it = d_literalTypeRules.find(k);
  if (it==d_literalTypeRules.end())
  {
    std::stringstream ss;
    EO_FATAL() << "TypeChecker::getOrSetLiteralTypeRule: cannot get type rule for kind "
                 << k;
  }
  if (it->second.isNull())
  {
    // If no type rule, assign the type rule to the builtin type
    Expr t = d_state.mkBuiltinType(k);
    d_literalTypeRules[k] = t;
    return t.getValue();
  }
  return it->second.getValue();
}

Expr TypeChecker::getType(Expr& e, std::ostream* out)
{
  std::map<const ExprValue*, Expr>::iterator itt;
  std::unordered_set<ExprValue*> visited;
  std::vector<ExprValue*> toVisit;
  toVisit.push_back(e.getValue());
  ExprValue* cur;
  Expr ret;
  std::map<const ExprValue*, Expr>& tc = d_state.d_typeCache;
  do
  {
    cur = toVisit.back();
    itt = tc.find(cur);
    if (itt != tc.end())
    {
      ret = itt->second;
      // already computed type
      toVisit.pop_back();
      continue;
    }
    if (visited.find(cur)==visited.end())
    {
      visited.insert(cur);
      toVisit.insert(toVisit.end(), cur->d_children.begin(), cur->d_children.end());
    }
    else
    {
      //std::cout << "Type check " << cur << std::endl;
      ret = getTypeInternal(cur, out);
      if (ret.isNull())
      {
        // any subterm causes type checking to fail
        Trace("type_checker")
            << "TYPE " << Expr(cur) << " : [FAIL]" << std::endl;
        return ret;
      }
      if (ret.isGround() && ret.isEvaluatable())
      {
        Trace("type_checker")
            << "TYPE " << Expr(cur) << " : [FAIL] due to evaluatable " << ret << std::endl;
        if (out)
        {
          (*out) << "Has type " << ret << " whose evaluation cannot be reduced";
        }
        return d_null;
      }
      tc[cur] = ret;
      Trace("type_checker")
          << "TYPE " << Expr(cur) << " : " << ret << std::endl;
      // std::cout << "...return" << std::endl;
      toVisit.pop_back();
    }
  }while (!toVisit.empty());
  return ret;
}

bool TypeChecker::checkArity(Kind k, size_t nargs, std::ostream* out)
{
  bool ret = false;
  // check arities
  switch(k)
  {
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_VAR:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_INT_MOD:
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_BIN:
    case Kind::EVAL_FIND:
    case Kind::EVAL_COMPARE:
    case Kind::EVAL_GT:
    case Kind::EVAL_LIST_LENGTH:
      ret = (nargs==2);
      break;
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    case Kind::EVAL_CONCAT:
      ret = (nargs>=2);
      break;
    case Kind::EVAL_LIST_CONCAT:
      ret = (nargs>=3);
      break;
    case Kind::PROOF_TYPE:
    case Kind::EVAL_TYPE_OF:
    case Kind::EVAL_NAME_OF:
    case Kind::EVAL_HASH:
    case Kind::EVAL_NOT:
    case Kind::EVAL_NEG:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_TO_RAT:
    case Kind::EVAL_TO_STRING:
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
    case Kind::EVAL_DT_CONSTRUCTORS:
    case Kind::EVAL_DT_SELECTORS: ret = (nargs == 1); break;
    case Kind::EVAL_NIL:
      ret = (nargs>=1);
      break;
    case Kind::EVAL_REQUIRES:
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
    case Kind::EVAL_LIST_FIND:
    case Kind::EVAL_LIST_NTH:
      ret = (nargs==3);
      break;
    case Kind::EVAL_EXTRACT:
      ret = (nargs==3 || nargs==2);
      break;
    default:
      if (out)
      {
        (*out) << "Unknown arity for " << k;
      }
      break;
  }
  if (!ret)
  {
    if (out)
    {
      (*out) << "Incorrect arity for " << k;
    }
    return false;
  }
  return true;
}

Expr TypeChecker::getTypeInternal(ExprValue* e, std::ostream* out)
{
  Kind k = e->getKind();
  switch(k)
  {
    case Kind::APPLY:
    case Kind::APPLY_OPAQUE:
    {
      Ctx ctx;
      return getTypeAppInternal(e->d_children, ctx, out);
    }
    case Kind::LAMBDA:
    {
      std::vector<Expr> args;
      std::vector<ExprValue*>& vars = e->d_children[0]->d_children;
      for (ExprValue* v : vars)
      {
        ExprValue* t = d_state.lookupType(v);
        Assert(t != nullptr);
        args.emplace_back(t);
      }
      Expr ret(d_state.lookupType(e->d_children[1]));
      Assert(!ret.isNull());
      return d_state.mkFunctionType(args, ret);
    }
    case Kind::TYPE:
    case Kind::ABSTRACT_TYPE:
    case Kind::BOOL_TYPE:
    case Kind::FUNCTION_TYPE:
      return d_state.mkType();
    case Kind::PROOF_TYPE:
    {
      ExprValue* ctype = d_state.lookupType(e->d_children[0]);
      Assert(ctype != nullptr);
      if (ctype->getKind()!=Kind::BOOL_TYPE)
      {
        if (out)
        {
          (*out) << "Non-Bool for argument of Proof";
        }
        return d_null;
      }
    }
      return d_state.mkType();
    case Kind::QUOTE_TYPE:
      // anything can be quoted
      return d_state.mkType();
    case Kind::OPAQUE_TYPE:
    {
      ExprValue* ctype = d_state.lookupType(e->d_children[0]);
      Assert(ctype != nullptr);
      if (ctype->getKind()!=Kind::TYPE)
      {
        if (out)
        {
          (*out) << "Non-Type for argument of opaque type";
        }
        return d_null;
      }
    }
      return d_state.mkType();
    case Kind::TUPLE:
      // not typed
      return d_state.mkAbstractType();
    case Kind::BOOLEAN:
      // note that Bool is builtin
      return d_state.mkBoolType();
    case Kind::NUMERAL:
    case Kind::DECIMAL:
    case Kind::RATIONAL:
    case Kind::HEXADECIMAL:
    case Kind::BINARY:
    case Kind::STRING:
    {
      // use the literal type rule
      ExprValue* ret = getOrSetLiteralTypeRule(k);
      // it may involve the "self" parameter
      if (!ret->isGround())
      {
        Ctx ctx;
        ctx[d_state.mkSelf().getValue()] = e;
        return evaluate(ret, ctx);
      }
      return Expr(ret);
    }
      break;
    case Kind::AS:
    {
      // constructing an application of AS means the type was incorrect.
      if (out)
      {
        (*out) << "Encountered bad type for eo::as";
      }
      return d_null;
    }
      break;
    case Kind::PARAMETERIZED:
    {
      // type of the second child
      return Expr(d_state.lookupType(e->d_children[1]));
    }
      break;
    default:
      // if a literal operator, consult auxiliary method
      if (isLiteralOp(k))
      {
        std::vector<ExprValue*> ctypes;
        std::vector<ExprValue*>& children = e->d_children;
        for (ExprValue* c : children)
        {
          ctypes.push_back(d_state.lookupType(c));
        }
        return Expr(getLiteralOpType(k, children, ctypes, out));
      }
      break;
  }
  if (out)
  {
    (*out) << "Unknown kind " << k;
  }
  return d_null;
}

Expr TypeChecker::getTypeApp(std::vector<Expr>& children, std::ostream* out)
{
  std::vector<ExprValue*> vchildren;
  for (const Expr& c : children)
  {
    vchildren.push_back(c.getValue());
  }
  Ctx ctx;
  return getTypeAppInternal(vchildren, ctx, out);
}

Expr TypeChecker::getTypeAppInternal(std::vector<ExprValue*>& children,
                                     Ctx& ctx,
                                     std::ostream* out)
{
  Assert (!children.empty());
  ExprValue* hd = children[0];
  ExprValue* hdType = d_state.lookupType(hd);
  Assert(hdType != nullptr) << "No type for " << Expr(hd);
  if (hdType->getKind()!=Kind::FUNCTION_TYPE)
  {
    // non-function at head
    if (out)
    {
      (*out) << "Non-function " << Expr(hd) << " as head of APPLY";
    }
    return d_null;
  }
  std::vector<ExprValue*> hdtypes = hdType->d_children;
  std::vector<ExprValue*> ctypes;
  if (hdtypes.size() != children.size())
  {
    // incorrect arity
    if (out)
    {
      (*out) << "Incorrect arity for " << Expr(hd);
      if (hdtypes[hdtypes.size() - 1]->getKind() == Kind::PROOF_TYPE)
      {
        // proof rule can give more information, partioned into args/premises
        size_t npIndex1 = hdtypes.size() - 1;
        while (npIndex1 > 0
               && hdtypes[npIndex1 - 1]->getKind() == Kind::PROOF_TYPE)
        {
          npIndex1--;
        }
        size_t npIndex2 = children.size() - 1;
        while (npIndex2 > 0
               && d_state.lookupType(children[npIndex2 - 1])->getKind()
                      == Kind::PROOF_TYPE)
        {
          npIndex2--;
        }
        (*out) << ", which expects " << npIndex1 << " arguments and "
               << (hdtypes.size() - 1 - npIndex1) << " premises but "
               << npIndex2 << " arguments and "
               << (children.size() - 1 - npIndex2) << " premises were provided";
      }
      else
      {
        (*out) << ", which expects " << (hdtypes.size() - 1)
               << " arguments but " << (children.size() - 1)
               << " were provided";
      }
    }
    return d_null;
  }
  for (size_t i=1, nchild=children.size(); i<nchild; i++)
  {
    Assert (children[i]!=nullptr);
    // if the argument type is (Quote t), then we implicitly upcast
    // the argument c to (quote c). This is equivalent to matching
    // c to t directly, hence we take the child itself and not its
    // type.
    ExprValue* arg;
    if (hdtypes[i-1]->getKind()==Kind::QUOTE_TYPE)
    {
      // don't need to evaluate
      arg = children[i];
    }
    else
    {
      arg = d_state.lookupType(children[i]);
      Assert(arg != nullptr);
    }
    ctypes.emplace_back(arg);
  }
  // if plugin can evaluate, run the compiled version of the type checker
  if (d_plugin!=nullptr && d_plugin->hasEvaluation(hdType))
  {
    Trace("type_checker") << "RUN type check " << Expr(hdType) << std::endl;
    return d_plugin->getType(hdType, ctypes, out);
  }
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  Expr hdEval;
  for (size_t i=0, nchild=ctypes.size(); i<nchild; i++)
  {
    Assert(ctypes[i] != nullptr);
    // matching, update context
    ExprValue* hdt = hdtypes[i];
    // if the argument is (Quote t), we match on its argument,
    // which along with how ctypes[i] is the argument itself, has the effect
    // of an implicit upcast.
    hdt = hdt->getKind() == Kind::QUOTE_TYPE ? hdt->d_children[0] : hdt;
    // must evaluate here
    if (hdt->isEvaluatable())
    {
      hdEval = evaluate(hdt, ctx);
      hdt = hdEval.getValue();
    }
    if (!match(hdt, ctypes[i], ctx, visited))
    {
      if (out)
      {
        ExprValue* hdto = hdtypes[i];
        if (hdtypes[i]->getKind() == Kind::QUOTE_TYPE)
        {
          (*out) << "Unexpected child #" << i << std::endl;
          (*out) << "  Term: " << Expr(children[i + 1]) << std::endl;
          (*out) << "  Expected pattern: ";
          hdto = hdto->d_children[0];
        }
        else
        {
          (*out) << "Unexpected type of child #" << i << std::endl;
          (*out) << "  Term: " << Expr(children[i + 1]) << std::endl;
          (*out) << "  Has type: " << Expr(ctypes[i]) << std::endl;
          (*out) << "  Expected type: ";
        }
        (*out) << Expr(hdt);
        if (hdto != hdt)
        {
          (*out) << ", from " << Expr(hdto);
        }
        (*out) << std::endl;
        (*out) << "  Context " << ctx << std::endl;
      }
      return d_null;
    }
  }
  // evaluate in the matched context
  return evaluate(hdtypes.back(), ctx);
}

bool TypeChecker::match(ExprValue* a, ExprValue* b, Ctx& ctx)
{
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  return match(a, b, ctx, visited);
}

bool TypeChecker::match(ExprValue* a,
                        ExprValue* b,
                        Ctx& ctx,
                        std::set<std::pair<ExprValue*, ExprValue*>>& visited)
{
  std::set<std::pair<ExprValue*, ExprValue*>>::iterator it;
  std::map<ExprValue*, ExprValue*>::iterator ctxIt;

  std::vector<std::pair<ExprValue*, ExprValue*>> stack;
  stack.emplace_back(a, b);
  std::pair<ExprValue*, ExprValue*> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      // holds trivially
      continue;
    }
    it = visited.find(curr);
    if (it != visited.end())
    {
      // already processed
      continue;
    }
    visited.insert(curr);
    if (curr.first->getNumChildren() == 0)
    {
      // if the two subterms are not equal and the first one is a bound
      // variable...
      if (curr.first->getKind() == Kind::PARAM)
      {
        // and we have not seen this variable before...
        ctxIt = ctx.find(curr.first);
        if (ctxIt == ctx.cend())
        {
          // note that we do not ensure the types match here
          // add the two subterms to `sub`
          ctx.emplace(curr.first, curr.second);
        }
        else if (ctxIt->second!=curr.second)
        {
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          return false;
        }
      }
      else
      {
        // the two subterms are not equal
        return false;
      }
    }
    else
    {
      // if the two subterms are not equal, make sure that their operators are
      // equal
      if (curr.first->getNumChildren() != curr.second->getNumChildren()
          || curr.first->getKind() != curr.second->getKind())
      {
        return false;
      }
      // recurse on children
      for (size_t i = 0, n = curr.first->getNumChildren(); i < n; ++i)
      {
        stack.emplace_back((*curr.first)[i], (*curr.second)[i]);
      }
    }
  }
  return true;
}

/** Evaluation frame, used in evaluate below. */
class EvFrame
{
 public:
  EvFrame(ExprValue* i, Ctx& ctx, ExprTrie* r) : d_init(i), d_ctx(ctx), d_result(r) {
    if (d_init!=nullptr)
    {
      d_visit.push_back(d_init);
    }
  }
  ~EvFrame(){}
  /** The initial value we are evaluating */
  ExprValue* d_init;
  /** The context it is being evaluated in */
  Ctx d_ctx;
  /** Cache of visited subterms */
  std::unordered_map<ExprValue*, Expr> d_visited;
  /** The subterms to visit */
  std::vector<ExprValue*> d_visit;
  /** An (optional) pointer of a trie of where to store the result */
  ExprTrie * d_result;
};

Expr TypeChecker::evaluate(ExprValue* e, Ctx& ctx)
{
  Assert (e!=nullptr);
  // A trie for all programs/oracles we have evaluated during this call.
  // This is required to ensure that programs that traverse terms recursively
  // preform a dag traversal.
  ExprTrie evalTrie;
  // A set of terms that we are manually incrementing their ref count (via
  // adding them to keepList). This set of terms includes the terms that
  // appear in the above trie.
  std::unordered_set<ExprValue*> keep;
  std::vector<Expr> keepList;
  std::unordered_map<ExprValue*, Expr>::iterator it;
  Ctx::iterator itc;
  // the evaluation stack
  std::vector<EvFrame> estack;
  estack.emplace_back(e, ctx, nullptr);
  Expr evaluated;
  ExprValue* cur;
  Kind ck;
  bool newContext = false;
  bool canEvaluate = true;
  while (!estack.empty())
  {
    EvFrame& evf = estack.back();
    std::unordered_map<ExprValue*, Expr>& visited = evf.d_visited;
    std::vector<ExprValue*>& visit = evf.d_visit;
    Ctx& cctx = evf.d_ctx;
    while (!visit.empty())
    {
      Assert (!newContext && canEvaluate);
      cur = visit.back();
      Trace("type_checker_debug") << "visit " << Expr(cur) << " " << cctx
                                  << ", depth=" << estack.size() << std::endl;
      // the term will stay the same if it is not evaluatable and either it
      // is ground, or the context is empty.
      if (!cur->isEvaluatable() && (cur->isGround() || cctx.empty()))
      {
        //std::cout << "...shortcut " << cur << std::endl;
        visited[cur] = Expr(cur);
        visit.pop_back();
        continue;
      }
      if (cur->getKind()==Kind::PARAM)
      {
        // might be in context
        itc = cctx.find(cur);
        if (itc!=cctx.end())
        {
          visited[cur] = Expr(itc->second);
          visit.pop_back();
          continue;
        }
        visited[cur] = Expr(cur);
        visit.pop_back();
        continue;
        // NOTE: this could be an error or warning, variable not filled
        //std::cout << "WARNING: unfilled variable " << cur << std::endl;
      }
      ck = cur->getKind();
      std::vector<ExprValue*>& children = cur->d_children;
      it = visited.find(cur);
      if (it == visited.end())
      {
        // if it is compiled, we run its evaluation here
        if (d_plugin && d_plugin->hasEvaluation(cur))
        {
          Trace("type_checker") << "RUN evaluate " << cur << std::endl;
          Expr retev = d_plugin->evaluate(cur, cctx);
          Assert(!retev.isNull());
          if (!retev.isNull())
          {
            Trace("type_checker") << "...returns " << retev << std::endl;
            visited[cur] = retev;
            visit.pop_back();
            continue;
          }
          // if we failed running via compiled, revert for now
          Trace("type_checker") << "...returns null" << std::endl;
        }
        // otherwise, visit children
        visited[cur] = d_null;
        if (ck==Kind::EVAL_IF_THEN_ELSE)
        {
          // if it is malformed, it does not evaluate
          if (children.size()!=3)
          {
            visited[cur] = Expr(cur);
            visit.pop_back();
            continue;
          }
          // special case: visit only the condition
          visit.push_back(children[0]);
        }
        else
        {
          visit.insert(visit.end(), children.begin(), children.end());
        }
        continue;
      }
      if (it->second.isNull())
      {
        std::vector<ExprValue*> cchildren;
        bool cchanged = false;
        for (ExprValue* cp : children)
        {
          it = visited.find(cp);
          if (it != visited.end())
          {
            cchildren.push_back(it->second.getValue());
            if (!cchanged)
            {
              cchanged = (cp!=it->second.getValue());
            }
          }
          else
          {
            // we won't evaluate on this iteration
            cchildren.push_back(nullptr);
          }
        }
        evaluated = d_null;
        switch (ck)
        {
          case Kind::APPLY:
          case Kind::APPLY_OPAQUE:
          {
            Trace("type_checker_debug")
                << "evaluated args " << cchildren << std::endl;
            // if a program and all arguments are ground, run it
            Kind cck = cchildren[0]->getKind();
            if (cck==Kind::PROGRAM_CONST || cck==Kind::ORACLE)
            {
              // maybe the evaluation is already cached
              // ensure things in the evalTrie are ref counted
              for (ExprValue* e : cchildren)
              {
                if (keep.insert(e).second)
                {
                  keepList.emplace_back(e);
                }
              }
              ExprTrie* et = evalTrie.get(cchildren);
              if (et->d_data!=nullptr)
              {
                evaluated = Expr(et->d_data);
                Trace("type_checker_debug")
                    << "evaluated via cached evaluation" << std::endl;
              }
              else
              {
                Ctx newCtx;
                // see if we evaluate
                evaluated = evaluateProgramInternal(cchildren, newCtx);
                //std::cout << "Evaluate prog returned " << evaluated << std::endl;
                if (evaluated.isNull() || evaluated.isGround() || newCtx.empty())
                {
                  // if the evaluation can be shortcircuited, don't need to
                  // push a context
                  // store the base evaluation (if applicable)
                  et->d_data = evaluated.getValue();
                }
                else
                {
                  // otherwise push an evaluation scope
                  newContext = true;
                  estack.emplace_back(evaluated.getValue(), newCtx, et);
                }
              }
            }
          }
            break;
          case Kind::EVAL_IF_THEN_ELSE:
          {
            Assert (cchildren[0]!=nullptr);
            Assert (children.size()==3);
            // get the evaluation of the condition
            if (cchildren[0]->getKind()==Kind::BOOLEAN)
            {
              const Literal* l = cchildren[0]->asLiteral();
              // inspect the relevant child only
              size_t index = l->d_bool ? 1 : 2;
              if (cchildren[index] == nullptr)
              {
                canEvaluate = false;
                // evaluate the child if not yet done so
                visit.push_back(children[index]);
              }
              else
              {
                evaluated = Expr(cchildren[index]);
                Trace("type_checker_debug") << "evaluated via ite" << std::endl;
              }
            }
            else
            {
              // note we must evaluate the children so that e.g. beta-reduction
              // and more generally substitution is accurate for non-ground
              // terms.
              for (size_t i=1; i<3; i++)
              {
                if (cchildren[i]==nullptr)
                {
                  // evaluate the child if not yet done so
                  visit.push_back(children[i]);
                  // can't evaluate yet if we aren't finished evaluating
                  canEvaluate = false;
                }
              }
            }
          }
            break;
          default:
            if (isLiteralOp(ck))
            {
              evaluated = evaluateLiteralOpInternal(ck, cchildren);
              Trace("type_checker_debug")
                  << "evaluated via literal op" << std::endl;
            }
            break;
        }
        if (newContext)
        {
          Trace("type_checker_debug") << "new context" << std::endl;
          break;
        }
        if (canEvaluate)
        {
          if (evaluated.isNull())
          {
            if (cchanged)
            {
              evaluated = Expr(d_state.mkExprInternal(ck, cchildren));
            }
            else
            {
              // children didn't change, just take the original
              evaluated = Expr(cur);
            }
            Trace("type_checker_debug")
                << "evaluated via mkExprInternal" << std::endl;
          }
          visited[cur] = evaluated;
          Trace("type_checker_debug")
              << "visited " << Expr(cur) << " = " << evaluated << std::endl;
          visit.pop_back();
        }
        else
        {
          canEvaluate = true;
          Trace("type_checker_debug") << "cannot evaluate" << std::endl;
        }
      }
      else
      {
        visit.pop_back();
      }
    }
    // if we are done evaluating the current context
    if (!newContext)
    {
      // get the result from the inner evaluation
      ExprValue* init = evf.d_init;
      Assert (evf.d_visited.find(init)!=evf.d_visited.end());
      evaluated = evf.d_visited[init];
      Trace("type_checker") << "EVALUATE " << Expr(init) << ", "
                            << evf.d_ctx << " = " << evaluated << std::endl;
      if (evf.d_result!=nullptr)
      {
        ExprValue * ev = evaluated.getValue();
        if (keep.insert(ev).second)
        {
          keepList.emplace_back(ev);
        }
        evf.d_result->d_data = ev;
      }
      // pop the evaluation context
      estack.pop_back();
      // carry to lower context
      if (!estack.empty())
      {
        EvFrame& evp = estack.back();
        Assert (!evp.d_visit.empty());
        evp.d_visited[evp.d_visit.back()] = evaluated;
        evp.d_visit.pop_back();
      }
    }
    else
    {
      newContext = false;
    }
  }
  return evaluated;
}

Expr TypeChecker::evaluateProgram(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  const Expr& ret = evaluateProgramInternal(children, newCtx);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(Kind::APPLY, children));
}

bool TypeChecker::isGround(const std::vector<ExprValue*>& args)
{
  for (ExprValue* e : args)
  {
    if (!e->isGround())
    {
      return false;
    }
  }
  return true;
}

Expr TypeChecker::evaluateProgramInternal(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  if (!isGround(children))
  {
    // do not evaluate on non-ground
    return d_null;
  }
  ExprValue* hd = children[0];
  Kind hk = hd->getKind();
  if (hk==Kind::PROGRAM_CONST)
  {
    if (d_plugin && d_plugin->hasEvaluation(hd))
    {
      Trace("type_checker") << "RUN program " << children << std::endl;
      return d_plugin->evaluateProgram(hd, children, newCtx);
    }
    size_t nargs = children.size();
    Expr prog = d_state.getProgram(hd);
    Assert (!prog.isNull());
    if (!prog.isNull())
    {
      Trace("type_checker") << "INTERPRET program " << children << std::endl;
      // otherwise, evaluate
      for (size_t i = 0, nchildren = prog.getNumChildren(); i < nchildren;
           i++)
      {
        const Expr& c = prog[i];
        newCtx.clear();
        ExprValue* hd = c[0].getValue();
        std::vector<ExprValue*>& hchildren = hd->d_children;
        if (nargs != hchildren.size())
        {
          // TODO: catch this during weak type checking of program bodies
          Warning() << "*** Bad number of arguments provided in function call to " << hd << std::endl;
          Warning() << "  Arguments: " << children << std::endl;
          return d_null;
        }
        bool matchSuccess = true;
        for (size_t i=1; i<nargs; i++)
        {
          if (!match(hchildren[i], children[i], newCtx))
          {
            matchSuccess = false;
            break;
          }
        }
        if (matchSuccess)
        {
          Trace("type_checker")
              << "...matches " << Expr(hd) << ", ctx = " << newCtx << std::endl;
          return c[1];
        }
      }
      Trace("type_checker") << "...failed to match." << std::endl;
    }
  }
  else if (hk==Kind::ORACLE)
  {
#ifdef EO_ORACLES
    // get the command
    std::string ocmd;
    if (!d_state.getOracleCmd(hd, ocmd))
    {
      return d_null;
    }
    int retVal;
#if 1
    std::stringstream call_content;
    call_content << "(" << std::endl;
    for (size_t i = 1, nchildren = children.size(); i < nchildren; i++)
    {
      call_content << Expr(children[i]) << std::endl;
    }
    call_content << ")" << std::endl;
    Trace("oracles") << "Call oracle " << ocmd << " with content:" << std::endl;
    Trace("oracles") << "```" << std::endl;
    Trace("oracles") << call_content.str() << std::endl;
    Trace("oracles") << "```" << std::endl;
    std::stringstream response;
    retVal = run(ocmd, call_content.str(), response);
#else
    std::stringstream call;
    call << ocmd;
    for (size_t i = 1, nchildren = children.size(); i < nchildren; i++)
    {
      call << " " << Expr(children[i]);
    }
    Trace("oracles") << "Call oracle " << ocmd << " with content:" << std::endl;
    Trace("oracles") << "```" << std::endl;
    Trace("oracles") << call.str() << std::endl;
    Trace("oracles") << "```" << std::endl;
    std::stringstream response;
    retVal = runFile(call.str(), response);
#endif
    if (retVal!=0)
    {
      Trace("oracles") << "...failed to run" << std::endl;
      return d_null;
    }
    Trace("oracles") << "...got response \"" << response.str() << "\"" << std::endl;
    Parser poracle(d_state);
    poracle.setStringInput(response.str());
    Expr ret = poracle.parseNextExpr();
    Trace("oracles") << "returns " << ret << std::endl;
    return ret;
#else /* EO_ORACLES */
    Trace("oracles") << "...not supported in this build" << std::endl;
    return d_null;
#endif /* EO_ORACLES */
  }
  // just return nullptr, which should be interpreted as a failed evaluation
  return d_null;
}

Expr TypeChecker::evaluateLiteralOp(Kind k,
                                    const std::vector<ExprValue*>& args)
{
  Expr ret = evaluateLiteralOpInternal(k, args);
  if (!ret.isNull())
  {
    return ret;
  }
  // otherwise does not evaluate, return application
  return Expr(d_state.mkExprInternal(k, args));
}

/**
 * Get nary children, gets a list of children from op-application e
 * up to maxChildren (0 means no limit), stores them in children.
 */
ExprValue* getNAryChildren(ExprValue* e,
                           ExprValue* op,
                           ExprValue* checkNil,
                           std::vector<ExprValue*>& children,
                           bool isLeft,
                           size_t maxChildren=0)
{
  ExprValue* orig = e;
  while (e->getKind()==Kind::APPLY)
  {
    ExprValue* cop = (*e)[0];
    if (cop->getKind()!=Kind::APPLY)
    {
      break;
    }
    if ((*cop)[0] != op)
    {
      break;
    }
    // push back the element
    children.push_back(isLeft ? (*e)[1] : (*cop)[1]);
    // traverse to tail
    e = isLeft ? (*cop)[1] : (*e)[1];
    if (children.size()==maxChildren)
    {
      return e;
    }
  }
  // must be equal to the nil term, if provided
  if (checkNil!=nullptr && e!=checkNil)
  {
    Warning() << "...expected associative application to end in " << Expr(checkNil) << ", got " << Expr(orig) << std::endl;
    return nullptr;
  }
  return e;
}

Expr TypeChecker::evaluateLiteralOpInternal(
    Kind k, const std::vector<ExprValue*>& args)
{
  Assert (!args.empty());
  Trace("type_checker") << "EVALUATE-LIT " << k << " " << args << std::endl;
  switch (k)
  {
    case Kind::EVAL_IS_EQ:
    {
      Assert (args.size()==2);
      bool ret = args[0]==args[1];
      if (ret)
      {
        // eagerly evaluate if sides are equal, even if non-ground
        return d_state.mkTrue();
      }
      else if (isGround(args))
      {
        // otherwise, if both sides are ground, we evaluate to false.
        // note this is independent of whether they are values.
        return d_state.mkFalse();
      }
      return d_null;
    }
    break;
    case Kind::EVAL_IF_THEN_ELSE:
    {
      Assert (args.size()==3);
      if (args[0]->getKind()==Kind::BOOLEAN)
      {
        const Literal* l = args[0]->asLiteral();
        // eagerly evaluate even if branches are non-ground
        return Expr(args[l->d_bool ? 1 : 2]);
      }
      // note that we do not simplify based on the branches being equal
      return d_null;
    }
    break;
    case Kind::EVAL_REQUIRES:
    {
      if (args[0]==args[1])
      {
        // eagerly evaluate even if body is non-ground
        return Expr(args[2]);
      }
      if (TraceIsOn("type_checker"))
      {
        if (isGround(args))
        {
          Trace("type_checker") << "REQUIRES: failed " << Expr(args[0])
                                << " == " << Expr(args[1]) << std::endl;
        }
      }
      return d_null;
    }
    break;
    case Kind::EVAL_HASH:
    {
      if (args[0]->isGround())
      {
        size_t h = d_state.getHash(args[0]);
        Literal lh(Integer(static_cast<unsigned int>(h)));
        return Expr(d_state.mkLiteralInternal(lh));
      }
      return d_null;
    }
    break;
    case Kind::EVAL_COMPARE:
    {
      if (args[0]->isGround() && args[1]->isGround())
      {
        size_t h1 = d_state.getHash(args[0]);
        size_t h2 = d_state.getHash(args[1]);
        Literal lb(h1>h2);
        return Expr(d_state.mkLiteralInternal(lb));
      }
      return d_null;
    }
    break;
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
    {
      if (!args[0]->isGround())
      {
        return d_null;
      }
      Kind kk;
      switch (k)
      {
      case Kind::EVAL_IS_Z:kk = Kind::NUMERAL;break;
      case Kind::EVAL_IS_Q:kk = Kind::RATIONAL;break;
      case Kind::EVAL_IS_BIN:kk = Kind::BINARY;break;
      case Kind::EVAL_IS_STR:kk = Kind::STRING;break;
      case Kind::EVAL_IS_BOOL:kk = Kind::BOOLEAN;break;
      case Kind::EVAL_IS_VAR:kk = Kind::VARIABLE;break;
      default:
        return d_null;
      }
      Literal lb(args[0]->getKind()==kk);
      return Expr(d_state.mkLiteralInternal(lb));
    }
    break;
    case Kind::EVAL_TYPE_OF:
    {
      // get the type if ground
      if (isGround(args))
      {
        Expr e(args[0]);
        return getType(e);
      }
      return d_null;
    }
    break;
    case Kind::EVAL_NAME_OF:
    {
      // get the type if ground
      if (isGround(args))
      {
        Kind k = args[0]->getKind();
        if (k==Kind::CONST || k==Kind::VARIABLE)
        {
          Literal sym(String(Expr(args[0]).getSymbol()));
          return Expr(d_state.mkLiteralInternal(sym));
        }
      }
      return d_null;
    }
    break;
    case Kind::EVAL_VAR:
    {
      // if arguments are ground and the first argument is a string
      if (args[0]->getKind()==Kind::STRING && args[1]->isGround())
      {
        Expr type(args[1]);
        Expr tt = getType(type);
        if (!tt.isNull() && tt.getKind()==Kind::TYPE)
        {
          const Literal* l = args[0]->asLiteral();
          return d_state.getBoundVar(l->d_str.toString(), type);
        }
      }
    }
    break;
    case Kind::EVAL_DT_CONSTRUCTORS:
    case Kind::EVAL_DT_SELECTORS:
    {
      // it may be an ambiguous constructor with an annotation, in which
      // case we extract the underlying symbol
      Expr sym(args[0]);
      sym = sym.getKind() == Kind::APPLY_OPAQUE ? sym[0] : sym;
      AppInfo* ac = d_state.getAppInfo(sym.getValue());
      if (ac != nullptr)
      {
        Assert(args[0]->isGround());
        Attr a = ac->d_attrCons;
        if ((a == Attr::DATATYPE && k == Kind::EVAL_DT_CONSTRUCTORS)
            || (a == Attr::DATATYPE_CONSTRUCTOR
                && k == Kind::EVAL_DT_SELECTORS))
        {
          return ac->d_attrConsTerm;
        }
      }
    }
    break;
    default:
      break;
  }
  if (!isGround(args))
  {
    Trace("type_checker") << "...does not evaluate (non-ground)" << std::endl;
    return d_null;
  }
  // convert argument expressions to literals
  std::vector<const Literal*> lits;
  bool allValues = true;
  for (ExprValue* e : args)
  {
    // symbols are stored as literals but do not evaluate
    if (!isLiteral(e->getKind()))
    {
      Trace("type_checker") << "...does not value-evaluate (argument)" << std::endl;
      // failed to convert an argument
      allValues = false;
      break;
    }
    lits.push_back(e->asLiteral());
  }
  // if all values, run the literal evaluator
  if (allValues)
  {
    if (!checkArity(k, args.size()))
    {
      Warning() << "Wrong number of arguments when applying literal op " << k
                << ", " << args.size() << " arguments (" << args << ")" << std::endl;
      // does not evaluate if arity is wrong
      return d_null;
    }
    // evaluate
    Literal eval = Literal::evaluate(k, lits);
    if (eval.getKind()==Kind::NONE)
    {
      Trace("type_checker") << "...does not value-evaluate (return)" << std::endl;
      // failed to evaluate
      return d_null;
    }
    // convert back to an expression
    Expr lit = Expr(d_state.mkLiteralInternal(eval));
    Trace("type_checker") << "...value-evaluates to " << lit << std::endl;
    return lit;
  }
  if (!isListLiteralOp(k))
  {
    return d_null;
  }
  // otherwise, maybe a list operation
  ExprValue* op = args[0];
  // strip off parameterized to look up AppInfo
  op = op->getKind()==Kind::PARAMETERIZED ? (*op)[1] : op;
  AppInfo* ac = d_state.getAppInfo(op);
  if (ac==nullptr)
  {
    Trace("type_checker") << "...not list op, return null" << std::endl;
    // not an associative operator
    return d_null;
  }
  Attr ck = ac->d_attrCons;
  if (ck!=Attr::RIGHT_ASSOC_NIL && ck!=Attr::LEFT_ASSOC_NIL)
  {
    // not an associative operator
    return d_null;
  }
  bool isLeft = (ck==Attr::LEFT_ASSOC_NIL);
  Trace("type_checker_debug") << "EVALUATE-LIT (list) " << k << " " << isLeft << " " << args << std::endl;
  // infer the nil expression, which depends on the type of args[1]
  std::vector<Expr> eargs;
  eargs.emplace_back(args[0]);
  if (args.size()>1)
  {
    eargs.emplace_back(args[1]);
  }
  Expr nilExpr = computeConstructorTermInternal(ac, eargs);
  if (nilExpr.isNull())
  {
    Trace("type_checker") << "...failed to get nil" << std::endl;
    return d_null;
  }
  ExprValue * nil = nilExpr.getValue();
  ExprValue* ret;
  std::vector<ExprValue*> hargs;
  switch (k)
  {
    case Kind::EVAL_NIL:
    {
      return nilExpr;
    }
    break;
    case Kind::EVAL_CONS:
    case Kind::EVAL_LIST_CONCAT:
    {
      bool isConcat = (k == Kind::EVAL_LIST_CONCAT);
      size_t tailIndex = (isLeft ? 1 : 2);
      size_t headIndex = (isLeft ? 2 : 1);
      ret = args[isConcat ? tailIndex : 2];
      std::vector<ExprValue*> targs;
      ExprValue* b = getNAryChildren(ret, op, nil, targs, isLeft);
      if (b==nullptr)
      {
        Trace("type_checker") << "...tail not in list form, nil is " << nilExpr << std::endl;
        // tail is not in list form
        return d_null;
      }
      if (k==Kind::EVAL_CONS)
      {
        hargs.push_back(args[1]);
      }
      else
      {
        // extract all children of the head
        ExprValue* a = getNAryChildren(args[headIndex], op, nil, hargs, isLeft);
        if (a==nullptr)
        {
          Trace("type_checker") << "...head not in list form" << std::endl;
          // head is not in list form
          return d_null;
        }
      }
      // note we take the tail verbatim
      std::vector<ExprValue*> cc;
      cc.push_back(op);
      cc.push_back(nullptr);
      cc.push_back(nullptr);
      for (size_t i = 0, nargs = hargs.size(); i < nargs; i++)
      {
        cc[tailIndex] = ret;
        cc[headIndex] = hargs[isLeft ? i : (nargs - 1 - i)];
        ret = d_state.mkApplyInternal(cc);
      }
      Trace("type_checker_debug")
          << "CONS: " << isLeft << " " << args << " -> " << ret << std::endl;
      return Expr(ret);
    }
      break;
    case Kind::EVAL_LIST_LENGTH:
    {
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft);
      if (a==nullptr)
      {
        Trace("type_checker") << "...head not in list form" << std::endl;
        return d_null;
      }
      Literal lret = Literal(Integer(hargs.size()));
      return Expr(d_state.mkLiteralInternal(lret));
    }
      break;
    case Kind::EVAL_LIST_NTH:
    {
      // (eo::extract <op> <term> <n>) returns the n^th child of <op>-application <term>
      if (args[2]->getKind()!=Kind::NUMERAL)
      {
        return d_null;
      }
      const Integer& index = args[2]->asLiteral()->d_int;
      if (!index.fitsUnsignedInt())
      {
        return d_null;
      }
      size_t i = index.toUnsignedInt();
      // extract up to i+1 children
      getNAryChildren(args[1], op, nil, hargs, isLeft, i+1);
      if (hargs.size()==i+1)
      {
        return Expr(hargs.back());
      }
      return d_null;
    }
      break;
    case Kind::EVAL_LIST_FIND:
    {
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft);
      if (a==nullptr)
      {
        Trace("type_checker") << "...head not in list form" << std::endl;
        return d_null;
      }
      std::vector<ExprValue*>::iterator it = std::find(hargs.begin(), hargs.end(), args[2]);
      if (it==hargs.end())
      {
        if (d_negOne.isNull())
        {
          Literal lno(Integer("-1"));
          d_negOne = Expr(d_state.mkLiteralInternal(lno));
        }
        return d_negOne;
      }
      size_t iret = std::distance(hargs.begin(), it);
      Literal lret = Literal(Integer(iret));
      return Expr(d_state.mkLiteralInternal(lret));
    }
      break;
    default:
      break;
  }
  return d_null;
}

ExprValue* TypeChecker::getLiteralOpType(Kind k,
                                         std::vector<ExprValue*>& children,
                                         std::vector<ExprValue*>& childTypes,
                                         std::ostream* out)
{
  if (!checkArity(k, childTypes.size(), out))
  {
    return d_null.getValue();
  }
  // NOTE: applications of most of these operators should only be in patterns,
  // where type checking is not strict.
  switch (k)
  {
    case Kind::EVAL_TYPE_OF:
      return d_state.mkType().getValue();
    case Kind::EVAL_VAR:
      // its type is the second argument
      return children[1];
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
      // NOTE: mixed arith
      return childTypes[0];
    case Kind::EVAL_NIL:
      // type is not computable here, since it is the return type of function
      // applications of the argument. just use abstract.
      return d_state.mkAbstractType().getValue();
    case Kind::EVAL_NEG:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    case Kind::EVAL_NOT:
      return childTypes[0];
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
      return childTypes[1];
    case Kind::EVAL_REQUIRES:
      return childTypes[2];
    case Kind::EVAL_LIST_CONCAT:
    case Kind::EVAL_LIST_NTH:
      return childTypes[1];
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_EXTRACT:
      // type is the first child
      return childTypes[0];
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_COMPARE:
    case Kind::EVAL_IS_Z:
    case Kind::EVAL_IS_Q:
    case Kind::EVAL_IS_BIN:
    case Kind::EVAL_IS_STR:
    case Kind::EVAL_IS_BOOL:
    case Kind::EVAL_IS_VAR:
      return d_state.mkBoolType().getValue();
    case Kind::EVAL_HASH:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_INT_MOD:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_FIND:
    case Kind::EVAL_LIST_LENGTH:
    case Kind::EVAL_LIST_FIND:
      return getOrSetLiteralTypeRule(Kind::NUMERAL);
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_RAT:
      return getOrSetLiteralTypeRule(Kind::RATIONAL);
    case Kind::EVAL_NAME_OF:
    case Kind::EVAL_TO_STRING:
      return getOrSetLiteralTypeRule(Kind::STRING);
    case Kind::EVAL_TO_BIN:
      return getOrSetLiteralTypeRule(Kind::BINARY);
    case Kind::EVAL_DT_CONSTRUCTORS:
    case Kind::EVAL_DT_SELECTORS: return d_state.mkListType().getValue();
    default:break;
  }
  if (out)
  {
    (*out) << "Unknown type for literal operator " << k;
  }
  return nullptr;
}

Expr TypeChecker::computeConstructorTermInternal(AppInfo* ai, 
                                                 const std::vector<Expr>& children)
{
  Expr hd;
  Expr nil;
  computedParameterizedInternal(ai, children, hd, nil);
  return nil;
}

bool TypeChecker::computedParameterizedInternal(AppInfo* ai,
                                                const std::vector<Expr>& children,
                                                Expr& hd,
                                                Expr& nil)
{
  hd = children[0];
  nil = d_null;
  if (ai==nullptr)
  {
    return true;
  }
  // lookup the base operator if necessary
  Expr ct = ai->d_attrConsTerm;
  if (ct.isNull() || ct.getKind()!=Kind::PARAMETERIZED)
  {
    // if not parameterized, just return self
    nil = ct;
    return true;
  }
  Trace("type_checker") << "Determine constructor term for " << hd << std::endl;
  // if explicit parameters, then evaluate the constructor term
  if (hd.getKind()!=Kind::PARAMETERIZED)
  {
    if (children.size()==1)
    {
      // if not in an application, we fail
      Warning() << "Failed to determine parameters for " << hd << std::endl;
      AlwaysAssert(false);
      return false;
    }
    else
    {
      // otherwise, we must infer the parameters
      Trace("type_checker") << "Infer params for " << hd << " @ " << children[1] << std::endl;
      if (isNAryAttr(ai->d_attrCons))
      {
        std::vector<ExprValue*> app;
        app.push_back(hd.getValue());
        app.push_back(children[1].getValue());
        // ensure children are type checked
        for (ExprValue* e : app)
        {
          Expr expr(e);
          getType(expr);
          ExprValue* t = d_state.lookupType(e);
          if (t==nullptr)
          {
            // only warn if ground
            if (expr.isGround())
            {
              Warning() << "Type inference failed for " << hd << " applied to " << children[1] << ", failed to type check " << expr << std::endl;
            }
            return false;
          }
          Trace("type_checker_debug") << "Type for " << expr << " is " << Expr(t) << std::endl;
        }
        Ctx tctx;
        getTypeAppInternal(app, tctx);
        Trace("type_checker_debug") << "Context was " << tctx << std::endl;
        std::vector<Expr> args;
        for (size_t i=0, nparams = ct[0].getNumChildren(); i<nparams; i++)
        {
          Expr cv(tctx[ct[0][i].getValue()]);
          if (cv.isNull())
          {
            Warning() << "Failed to find context for " << ct[0][i] << " when applying " << hd << " @ " << children[1] << std::endl;
            return false;
          }
          if (!cv.isGround())
          {
            // If the parameter is non-ground, we also wait to construct;
            // if the nil terminator is used, it will be replaced by a
            // placeholder involving eo::nil.
            return false;
          }
          args.emplace_back(cv);
        }
        // the head is now disambiguated
        hd = d_state.mkParameterized(hd.getValue(), args);
        Trace("type_checker_debug") << "Infered parameterized op " << hd << std::endl;
      }
      else
      {
        Warning() << "Unknown category for parameterized operator " << hd << std::endl;
        return false;
      }
    }
  }
  Assert (hd.getKind()==Kind::PARAMETERIZED);
  Ctx ctx;
  if (hd[0].getNumChildren()==ct[0].getNumChildren())
  {
    for (size_t i=0, nparams = hd[0].getNumChildren(); i<nparams; i++)
    {
      ctx[ct[0][i].getValue()] = hd[0][i].getValue();
    }
  }
  else
  {
    // error
    Warning() << "Unexpected number of parameters for " << hd[1]
              << ", expected " << ct.getNumChildren() << " parameters, got "
              << hd.getNumChildren() << std::endl;
    return false;
  }
  Trace("type_checker") << "Context for constructor term: " << ctx << std::endl;
  nil = evaluate(ct[1].getValue(), ctx);
  return true;
}

}  // namespace ethos
