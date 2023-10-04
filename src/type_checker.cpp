#include "type_checker.h"

#include <iostream>
#include <set>
#include <unordered_map>

#include "base/check.h"
#include "base/output.h"
#include "state.h"
#include "parser.h"
#include "literal.h"

namespace alfc {
  
std::ostream& operator<<(std::ostream& out, const Ctx& c)
{
  out << "[";
  bool firstTime = true;
  for (const std::pair<ExprValue* const, ExprValue*>& cc : c)
  {
    if (firstTime)
    {
      firstTime = false;
    }
    else
    {
      out << ", ";
    }
    out << Expr(cc.first) << " -> " << Expr(cc.second);
  }
  out << "]";
  return out;
}

TypeChecker::TypeChecker(State& s, Options& opts) : d_state(s)
{
  std::set<Kind> literalKinds = { Kind::BOOLEAN, Kind::NUMERAL, Kind::RATIONAL, Kind::BINARY, Kind::STRING };
  if (!opts.d_normalizeDecimal)
  {
    literalKinds.insert(Kind::DECIMAL);
  }  
  if (!opts.d_normalizeHexadecimal)
  {
    literalKinds.insert(Kind::HEXADECIMAL);
  }
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
    ALFC_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
                 << k;
  }
  else if (!it->second.isNull() && it->second != t)
  {
    std::stringstream ss;
    ALFC_FATAL() << "TypeChecker::setTypeRule: cannot set type rule for kind "
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
    ALFC_FATAL() << "TypeChecker::getOrSetLiteralTypeRule: cannot get type rule for kind "
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
    case Kind::NIL:
      ret = (nargs==0);
      break;
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_BV:
    case Kind::EVAL_FIND:
    case Kind::EVAL_CONS:
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
    case Kind::PROOF_TYPE:
    case Kind::EVAL_HASH:
    case Kind::EVAL_NOT:
    case Kind::EVAL_NEG:
    case Kind::EVAL_IS_NEG:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_TO_RAT:
    case Kind::EVAL_TO_STRING:
    case Kind::EVAL_TO_LIST:
    case Kind::EVAL_FROM_LIST:
      ret = (nargs==1);
      break;
    case Kind::EVAL_REQUIRES:
    case Kind::EVAL_IF_THEN_ELSE:
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
    {
      return getTypeAppInternal(e->d_children, out);
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
    case Kind::NIL:
      if (!checkArity(k, e->getNumChildren(), out))
      {
        return d_null;
      }
      // nil is its own type
      return Expr(e);
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
        return Expr(getLiteralOpType(k, ctypes, out));
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
  return getTypeAppInternal(vchildren, out);
}

Expr TypeChecker::getTypeAppInternal(std::vector<ExprValue*>& children,
                                     std::ostream* out)
{
  Assert (!children.empty());
  ExprValue* hd = children[0];
  ExprValue* hdType = d_state.lookupType(hd);
  Assert(hdType != nullptr);
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
      (*out) << "Incorrect arity for " << Expr(hd)
             << ", #argTypes=" << hdtypes.size()
             << " #children=" << children.size();
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
  // if compiled, run the compiled version of the type checker
  if (hdType->isCompiled())
  {
    Trace("type_checker") << "RUN type check " << Expr(hdType) << std::endl;
    return run_getTypeInternal(hdType, ctypes, out);
  }
  Ctx ctx;
  std::set<std::pair<ExprValue*, ExprValue*>> visited;
  for (size_t i=0, nchild=ctypes.size(); i<nchild; i++)
  {
    Assert(ctypes[i] != nullptr);
    // matching, update context
    ExprValue* hdt = hdtypes[i];
    // if the argument is (Quote t), we match on its argument,
    // which along with how ctypes[i] is the argument itself, has the effect
    // of an implicit upcast.
    hdt = hdt->getKind() == Kind::QUOTE_TYPE ? hdt->d_children[0] : hdt;
    if (!match(hdt, ctypes[i], ctx, visited))
    {
      if (out)
      {
        (*out) << "Unexpected argument type " << i << " of " << Expr(hd)
               << std::endl;
        (*out) << "  LHS " << evaluate(hdtypes[i], ctx) << ", from "
               << Expr(hdtypes[i]) << std::endl;
        (*out) << "  RHS " << Expr(ctypes[i]) << std::endl;
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
        if (cur->isCompiled())
        {
          Trace("type_checker") << "RUN evaluate " << cur << std::endl;
          Expr retev = run_evaluate(cur, cctx);
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
          {
            Trace("type_checker_debug")
                << "evaluated args " << cchildren << std::endl;
            // if a program and all arguments are ground, run it
            Kind cck = cchildren[0]->getKind();
            if (cck==Kind::PROGRAM_CONST || cck==Kind::ORACLE)
            {
              // maybe the evaluation is already cached
              // ensure things in the evalTrie are ref counted
              std::vector<ExprValue*> cchildrenh;
              for (ExprValue* e : cchildren)
              {
                ExprValue* eh = ensureHashed(e);
                if (keep.insert(eh).second)
                {
                  keepList.emplace_back(eh);
                }
                cchildrenh.push_back(eh);
              }
              ExprTrie* et = evalTrie.get(cchildrenh);
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
                evaluated = evaluateProgramInternal(cchildrenh, newCtx);
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
              //evaluated = Expr(d_state.mkExprInternal(ck, cchildren));
              evaluated = Expr(new ExprValue(ck, cchildren));
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
  return Expr(ensureHashed(evaluated.getValue()));
}

Expr TypeChecker::evaluateProgram(
    const std::vector<ExprValue*>& children, Ctx& newCtx)
{
  const Expr& ret = evaluateProgramInternal(children, newCtx);
  if (!ret.isNull())
  {
    return Expr(ensureHashed(ret.getValue()));
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

int run(const std::string& call, std::ostream& response)
{
  FILE* stream = popen(call.c_str(), "r");
  if (stream != nullptr)
  {
    int ch;
    while ((ch = fgetc(stream)) != EOF)
    {
      response << (unsigned char)ch;
    }
    return pclose(stream);
  }
  return -1;
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
    if (hd->isCompiled())
    {
      Trace("type_checker") << "RUN program " << children << std::endl;
      ExprValue* ret = run_evaluateProgram(children, newCtx);
      Trace("type_checker")
          << "...matches " << Expr(ret) << ", ctx = " << newCtx << std::endl;
      return Expr(ret);
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
    // get the command
    std::string ocmd;
    if (!d_state.getOracleCmd(hd, ocmd))
    {
      return d_null;
    }
    std::stringstream call;
    call << ocmd;
    for (size_t i=1, nchildren=children.size(); i<nchildren; i++)
    {
      call << " " << Expr(children[i]);
    }
    Trace("oracles") << "Call oracle " << ocmd << " with arguments:" << std::endl;
    Trace("oracles") << "```" << std::endl;
    Trace("oracles") << call.str() << std::endl;
    Trace("oracles") << "```" << std::endl;
    std::stringstream response;
    int retVal = run(call.str(), response);
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
    return Expr(ensureHashed(ret.getValue()));
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
      bool ret = ensureHashed(args[0])==ensureHashed(args[1]);
      if (ret)
      {
        // eagerly evaluate if sides and equal and non-ground
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
      if (ensureHashed(args[0])==ensureHashed(args[1]))
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
    case Kind::EVAL_HASH:
    {
      if (args[0]->isGround())
      {
        ExprValue* eh = ensureHashed(args[0]);
        size_t h = d_state.getHash(eh);
        //Literal lh(Integer(static_cast<unsigned int>(h)));
        return Expr(new Literal(Integer(static_cast<unsigned int>(h))));
      }
      return d_null;
    }
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
    // evaluate
    Literal eval = Literal::evaluate(k, lits);
    if (eval.getKind()==Kind::NONE)
    {
      Trace("type_checker") << "...does not value-evaluate (return)" << std::endl;
      // failed to evaluate
      return d_null;
    }
    // convert back to an expression
    Expr lit = Expr(new Literal(eval));
    Trace("type_checker") << "...value-evaluates to " << lit << std::endl;
    return lit;
  }
  // otherwise, maybe a list operation
  AppInfo* ac = d_state.getAppInfo(args[0]);
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
  ExprValue* op = args[0];
  ExprValue* nil = ac->d_attrConsTerm.getValue();
  size_t tailIndex = (isLeft ? 1 : 2);
  size_t headIndex = (isLeft ? 2 : 1);
  ExprValue* ret;
  std::vector<ExprValue*> hargs;
  switch (k)
  {
    case Kind::EVAL_TO_LIST:
    {
      ExprValue* harg = args[1];
      if (harg == nil)
      {
        // already nil
        return Expr(harg);
      }
      // check if already has children
      ExprValue* a = getNAryChildren(harg, op, nullptr, hargs, isLeft);
      if (!hargs.empty())
      {
        // already a list
        return Expr(harg);
      }
      else if (a==nullptr)
      {
        return d_null;
      }
      // otherwise, turn into singleton list
      ret = ac->d_attrConsTerm.getValue();
      hargs.push_back(a);
    }
      break;
    case Kind::EVAL_FROM_LIST:
    {
      // once we have >=2 children, we know this is a no-op
      ExprValue* a = getNAryChildren(args[1], op, nil, hargs, isLeft, 2);
      if (hargs.size()==1)
      {
        if (a==nullptr)
        {
          // unexpected nil terminator
          return d_null;
        }
        // eliminate singleton list
        return Expr(hargs[0]);
      }
      // otherwise self
      return Expr(args[1]);
    }
      break;
    case Kind::EVAL_CONS:
    case Kind::EVAL_CONCAT:
    {
      std::vector<ExprValue*> targs;
      ExprValue* b = getNAryChildren(args[tailIndex], op, nil, targs, isLeft);
      if (b==nullptr)
      {
        // tail is not in list form
        return d_null;
      }
      if (k==Kind::EVAL_CONS)
      {
        hargs.push_back(args[headIndex]);
      }
      else
      {
        // extract all children of the head
        ExprValue* a = getNAryChildren(args[headIndex], op, nil, hargs, isLeft);
        if (a==nullptr)
        {
          // head is not in list form
          return d_null;
        }
      }
      // note we take the tail verbatim
      ret = args[tailIndex];
    }
      break;
    case Kind::EVAL_EXTRACT:
    {
      // (alf.extract <op> <term> <n>) returns the n^th child of <op>-application <term>
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
    case Kind::EVAL_FIND:
    {
      getNAryChildren(args[1], op, nil, hargs, isLeft);
      std::vector<ExprValue*>::iterator it = std::find(hargs.begin(), hargs.end(), args[2]);
      if (it==hargs.end())
      {
        if (d_negOne.isNull())
        {
          d_negOne = Expr(new Literal(Integer("-1")));
        }
        return d_negOne;
      }
      size_t iret = std::distance(hargs.begin(), it);
      return Expr(new Literal(Integer(iret)));
    }
      break;
    default:
      // not a list operator
      return d_null;
      break;
  }
  std::vector<ExprValue*> cc;
  cc.push_back(op);
  cc.push_back(nullptr);
  cc.push_back(nullptr);
  for (size_t i=0, nargs=hargs.size(); i<nargs; i++)
  {
    cc[tailIndex] = ret;
    cc[headIndex] = hargs[isLeft ? i : (nargs-1-i)];
    ret = new ExprValue(Kind::APPLY, {cc[0], cc[1]});
    ret = new ExprValue(Kind::APPLY, {ret, cc[2]});
  }
  Trace("type_checker_debug") << "CONS: " << isLeft << " " << args << " -> " << ret << std::endl;
  return Expr(ret);
}

ExprValue* TypeChecker::ensureHashed(ExprValue* ev)
{
  if (ev->getFlag(ExprValue::Flag::IS_HASHED))
  {
    return ev;
  }
  std::unordered_map<ExprValue*, ExprValue*> visited;
  std::vector<ExprValue*> visit;
  std::unordered_map<ExprValue*, ExprValue*>::iterator it;
  visit.emplace_back(ev);
  ExprValue* cur;
  do
  {
    cur = visit.back();
    if (cur->getFlag(ExprValue::Flag::IS_HASHED))
    {
      visited[cur] = cur;
      visit.pop_back();
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      std::vector<ExprValue*>& children = cur->d_children;
      // otherwise, visit children
      visited[cur] = nullptr;
      visit.insert(visit.end(), children.begin(), children.end());
      continue;
    }
    visit.pop_back();
    if (it->second==nullptr)
    {
      Kind ck = cur->getKind();
      if (isLiteral(ck))
      {
        visited[cur] = d_state.mkLiteralInternal(*static_cast<Literal*>(cur));
      }
      else
      {
        Assert (!isSymbol(ck)) << "Not hashed : " << Expr(cur);
        std::vector<ExprValue*>& children = cur->d_children;
        std::vector<ExprValue*> cchildren;
        for (ExprValue* cp : children)
        {
          it = visited.find(cp);
          Assert (it != visited.end());
          cchildren.push_back(it->second);
        }
        visited[cur] = d_state.mkExprInternal(cur->getKind(), cchildren);
      }
    }
    // TODO: could optimize by deep updating cur's children
  }
  while (!visit.empty());
  return visited[ev];
}

ExprValue* TypeChecker::getLiteralOpType(Kind k,
                                         std::vector<ExprValue*>& childTypes,
                                         std::ostream* out)
{
  // operators with functions at the first index are "indexed
  size_t i = 0;
  if (!childTypes.empty() && childTypes[0]->getKind()==Kind::FUNCTION_TYPE)
  {
    // TODO: ensure the function is binary with same types
    i++;
  }
  if (!checkArity(k, childTypes.size()-i, out))
  {
    return d_null.getValue();
  }
  // NOTE: applications of most of these operators should only be in patterns,
  // where type checking is not strict.
  switch (k)
  {
    case Kind::EVAL_ADD:
    case Kind::EVAL_MUL:
      // NOTE: mixed arith
      return childTypes[0];
    case Kind::EVAL_NEG:
    case Kind::EVAL_AND:
    case Kind::EVAL_OR:
    case Kind::EVAL_XOR:
    case Kind::EVAL_NOT:
      return childTypes[0];
    case Kind::EVAL_IF_THEN_ELSE:
    case Kind::EVAL_CONS:
    case Kind::EVAL_TO_LIST:
    case Kind::EVAL_FROM_LIST:
      return childTypes[1];
    case Kind::EVAL_REQUIRES:
      return childTypes[2];
    case Kind::EVAL_CONCAT:
    case Kind::EVAL_EXTRACT:
      // type is the first child, maybe after a function
      return childTypes[i];
    case Kind::EVAL_IS_EQ:
    case Kind::EVAL_IS_NEG:
      return d_state.mkBoolType().getValue();
    case Kind::EVAL_HASH:
    case Kind::EVAL_INT_DIV:
    case Kind::EVAL_TO_INT:
    case Kind::EVAL_LENGTH:
    case Kind::EVAL_FIND:
      return getOrSetLiteralTypeRule(Kind::NUMERAL);
    case Kind::EVAL_RAT_DIV:
    case Kind::EVAL_TO_RAT:
      return getOrSetLiteralTypeRule(Kind::RATIONAL);
    default:break;
  }
  if (out)
  {
    (*out) << "Unknown type for literal operator " << k;
  }
  return nullptr;
}

}  // namespace alfc

