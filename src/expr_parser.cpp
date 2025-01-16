/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "expr_parser.h"

#include <string.h>

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "type_checker.h"

namespace ethos {

/**
 * Definition of state identifiers when parsing terms
 *
 * This is required for non-recursive parsing of terms. Note that in SMT-LIB,
 * terms generally are of the form (...anything not involving terms... <term>*)
 * However, let-terms, match-terms, and terms appearing within attributes
 * for term annotations are exceptions to this.
 * Thus, in the main parsing loop in parseExpr below, we require tracking
 * the context we are in, which dictates how to setup parsing the term after
 * the current one.
 *
 * In each state, the stack frame contains a list of arguments `d_args`, which
 * give a recipe for the term we are parsing. The interpretation of args depends
 * on the context we are in, as documented below.
 */
enum class ParseCtx
{
  NONE,
  /**
   * NEXT_ARG: in context (<op> <term>* <term>
   * `args` contain the accumulated list of arguments.
   */
  NEXT_ARG,
  /**
   * Let bindings
   *
   * LET_NEXT_BIND: in context (let (<binding>* (<symbol> <term>
   *
   * LET_BODY: in context (let (<binding>*) <term>
   */
  LET_NEXT_BIND,
  LET_BODY,
  /**
   * Match terms
   *
   * MATCH_HEAD: in context (match <term>
   *
   * MATCH_NEXT_CASE: in context (match <term> (<case>* (<pattern> <term>
   *                  or in context (match <term> (<case>* (<pattern>.
   * `args` contains the head, plus a list of arguments of the form
   * (TUPLE t1 t2), denoting the cases we have parsed. Optionally, the
   * last element of args is a (non-TUPLE) term denoting the pattern.
   */
  MATCH_HEAD,
  MATCH_NEXT_CASE,
  /**
   * Term annotations
   *
   * TERM_ANNOTATE_BODY: in context (! <term> <attribute>* <attribute>
   * `args` contains the term we parsed, which is modified based on the
   * attributes read.
   */
  TERM_ANNOTATE_BODY
};

ExprParser::ExprParser(Lexer& lex, State& state, bool isSignature)
    : d_lex(lex), d_state(state), d_isSignature(isSignature)
{
  d_strToAttr[":var"] = Attr::VAR;
  d_strToAttr[":implicit"] = Attr::IMPLICIT;
  d_strToAttr[":type"] = Attr::TYPE;
  d_strToAttr[":list"] = Attr::LIST;
  d_strToAttr[":requires"] = Attr::REQUIRES;
  d_strToAttr[":left-assoc"] = Attr::LEFT_ASSOC;
  d_strToAttr[":right-assoc"] = Attr::RIGHT_ASSOC;
  d_strToAttr[":left-assoc-nil"] = Attr::LEFT_ASSOC_NIL;
  d_strToAttr[":right-assoc-nil"] = Attr::RIGHT_ASSOC_NIL;
  d_strToAttr[":chainable"] = Attr::CHAINABLE;
  d_strToAttr[":pairwise"] = Attr::PAIRWISE;
  d_strToAttr[":binder"] = Attr::BINDER;
  d_strToAttr[":let-binder"] = Attr::LET_BINDER;
  d_strToAttr[":opaque"] = Attr::OPAQUE;
  d_strToAttr[":syntax"] = Attr::SYNTAX;
  d_strToAttr[":restrict"] = Attr::RESTRICT;
  d_strToAttr[":sorry"] = Attr::SORRY;
  
  d_strToLiteralKind["<boolean>"] = Kind::BOOLEAN;
  d_strToLiteralKind["<numeral>"] = Kind::NUMERAL;
  d_strToLiteralKind["<decimal>"] = Kind::DECIMAL;
  d_strToLiteralKind["<rational>"] = Kind::RATIONAL;
  d_strToLiteralKind["<hexadecimal>"] = Kind::HEXADECIMAL;
  d_strToLiteralKind["<binary>"] = Kind::BINARY;
  d_strToLiteralKind["<string>"] = Kind::STRING;
}

class StackFrame
{
public:
  StackFrame(ParseCtx ctx, size_t nscopes = 0) : 
    d_ctx(ctx), d_nscopes(nscopes) {}
  StackFrame(ParseCtx ctx, size_t nscopes, const std::vector<Expr>& args) : 
    d_ctx(ctx), d_nscopes(nscopes), d_args(args) {}
  ParseCtx d_ctx;
  size_t d_nscopes;
  std::vector<Expr> d_args;
  void pop(State& s)
  {
    // process the scope change
    for (size_t i=0; i<d_nscopes; i++)
    {
      s.popScope();
    }
  }
};

Expr ExprParser::parseExpr()
{
  // the last parsed term
  Expr ret;
  // a request was made to update the current parse context
  bool needsUpdateCtx = false;
  // the last token we read
  Token tok;
  // The stack(s) containing the parse context, the number of scopes, and the
  // arguments for the current expression we are building.
  std::vector<StackFrame> pstack;
  // Let bindings, dynamically allocated for each let in scope.
  std::vector<std::vector<std::pair<std::string, Expr>>> letBinders;
  do
  {
    // At this point, we are ready to parse the next term
    tok = d_lex.nextToken();
    Expr currExpr;
    switch (tok)
    {
      // ------------------- open paren
      case Token::LPAREN:
      {
        tok = d_lex.nextToken();
        switch (tok)
        {
          case Token::LET:
          case Token::EVAL_DEFINE:
          {
            pstack.emplace_back(ParseCtx::LET_NEXT_BIND);
            needsUpdateCtx = true;
            letBinders.emplace_back();
          }
          break;
          case Token::EVAL_MATCH:
          {
            // parse the variable list
            d_state.pushScope();
            std::vector<Expr> vs = parseAndBindSortedVarList();
            std::vector<Expr> args;
            args.emplace_back(d_state.mkExpr(Kind::TUPLE, vs));
            pstack.emplace_back(ParseCtx::MATCH_HEAD, 1, args);
          }
          break;
          case Token::ATTRIBUTE:
            pstack.emplace_back(ParseCtx::TERM_ANNOTATE_BODY);
            break;
          case Token::LPAREN:
          {
            // we allow the syntax ((_ to begin a term
            pstack.emplace_back(ParseCtx::NEXT_ARG);
            tok = d_lex.nextToken();
            if (tokenStrToSymbol(tok)!="_")
            {
              d_lex.parseError("Expected indexed symbol as head of apply");
            }
          }
          case Token::SYMBOL:
          case Token::QUOTED_SYMBOL:
          {
            // function identifier
            std::string name = tokenStrToSymbol(tok);
            std::vector<Expr> args;
            Expr v = getVar(name);
            args.push_back(v);
            size_t nscopes = 0;
            // if a binder, read a variable list and push a scope
            Attr ck = d_state.getConstructorKind(v.getValue());
            if (ck==Attr::BINDER || ck==Attr::LET_BINDER)
            {
              // If it is a binder, immediately read the bound variable list.
              // If option d_binderFresh is true, we parse and bind fresh
              // variables. Otherwise, we make calls to State::getBoundVar
              // meaning the bound variables are unique for each (name, type)
              // pair.
              // We only do this if there are two left parentheses. Otherwise we
              // will parse a tuple term that stands for a symbolic bound
              // variable list. We do this because there are no terms that
              // begin ((... currently allowed in this parser.
              // Note we use nextToken here since we cannot peek more than once.
              tok = d_lex.nextToken();
              if (tok==Token::LPAREN)
              {
                tok = d_lex.peekToken();
                d_lex.reinsertToken(Token::LPAREN);
                if (tok==Token::LPAREN)
                {
                  if (ck==Attr::BINDER)
                  {
                    nscopes = 1;
                    // we always do lookups if parsing signature
                    bool isLookup = d_isSignature || !d_state.getOptions().d_binderFresh;
                    d_state.pushScope();
                    std::vector<Expr> vs = parseAndBindSortedVarList(isLookup);
                    if (vs.empty())
                    {
                      d_lex.parseError("Expected non-empty sorted variable list");
                    }
                    Expr vl = d_state.mkBinderList(v.getValue(), vs);
                    args.push_back(vl);
                  }
                  else
                  {
                    Assert (ck==Attr::LET_BINDER);
                    nscopes = 1;
                    d_state.pushScope();
                    std::vector<std::pair<Expr, Expr>> lls = parseAndBindLetList();
                    if (lls.empty())
                    {
                      d_lex.parseError("Expected non-empty let list");
                    }
                    Expr vl = d_state.mkLetBinderList(v.getValue(), lls);
                    args.push_back(vl);
                  }
                }
              }
              else
              {
                d_lex.reinsertToken(tok);
              }
            }
            pstack.emplace_back(ParseCtx::NEXT_ARG, nscopes, args);
          }
          break;
          case Token::UNTERMINATED_QUOTED_SYMBOL:
            d_lex.parseError("Expected SMT-LIBv2 operator", true);
            break;
          default:
            d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 operator");
            break;
        }
      }
      break;
      // ------------------- close paren
      case Token::RPAREN:
      {
        StackFrame& sf = pstack.back();
        // should only be here if we are expecting arguments
        if (pstack.empty() || sf.d_ctx != ParseCtx::NEXT_ARG)
        {
          d_lex.unexpectedTokenError(
              tok, "Mismatched parentheses in SMT-LIBv2 term");
        }
        // Construct the application term specified by tstack.back()
        ret = d_state.mkExpr(Kind::APPLY, sf.d_args);
        //typeCheck(ret);
        // pop the stack
        sf.pop(d_state);
        pstack.pop_back();
      }
      break;
      // ------------------- base cases
      case Token::SYMBOL:
      case Token::QUOTED_SYMBOL:
      {
        std::string name = tokenStrToSymbol(tok);
        ret = getVar(name);
      }
      break;
      case Token::INTEGER_LITERAL:
      {
        // normalize to rational if not signature and option is set
        if (!d_isSignature && d_state.getOptions().d_normalizeNumeral)
        {
          Rational r(d_lex.tokenStr());
          ret = d_state.mkLiteral(Kind::RATIONAL, r.toString());
        }
        else
        {
          ret = d_state.mkLiteral(Kind::NUMERAL, d_lex.tokenStr());
        }
      }
      break;
      case Token::DECIMAL_LITERAL:
      {
        // normalize to rational if not signature and option is set
        if (!d_isSignature && d_state.getOptions().d_normalizeDecimal)
        {
          // normalize from decimal
          Rational r = Rational::fromDecimal(d_lex.tokenStr());
          ret = d_state.mkLiteral(Kind::RATIONAL, r.toString());
        }
        else
        {
          ret = d_state.mkLiteral(Kind::DECIMAL, d_lex.tokenStr());
        }
      }
      break;
      case Token::RATIONAL_LITERAL:
      {
        std::string s = d_lex.tokenStr();
        size_t spos = s.find('/');
        if (spos != std::string::npos)
        {
          // Ensure the denominator contains a non-zero digit. We catch this here to
          // avoid a floating point exception in GMP. This exception will be caught
          // and given the standard error message below.
          if (s.find_first_not_of('0', spos + 1) == std::string::npos)
          {
            d_lex.parseError("Expected non-zero denominator", true);
          }
        }
        ret = d_state.mkLiteral(Kind::RATIONAL, s);
      }
      break;
      case Token::HEX_LITERAL:
      {
        std::string hexStr = d_lex.tokenStr();
        hexStr = hexStr.substr(2);
        // normalize to binary if not signature and option is set
        if (!d_isSignature && d_state.getOptions().d_normalizeHexadecimal)
        {
          // normalize from hexadecimal
          BitVector bv(hexStr, 16);
          ret = d_state.mkLiteral(Kind::BINARY, bv.toString());
        }
        else
        {
          ret = d_state.mkLiteral(Kind::HEXADECIMAL, hexStr);
        }
      }
      break;
      case Token::BINARY_LITERAL:
      {
        std::string binStr = d_lex.tokenStr();
        binStr = binStr.substr(2);
        ret = d_state.mkLiteral(Kind::BINARY, binStr);
      }
      break;
      case Token::STRING_LITERAL:
      {
        std::string s = d_lex.tokenStr();
        unescapeString(s);
        // now, must run through String utility so that its unicode
        // handling is unique
        String str(s, true);
        ret = d_state.mkLiteral(Kind::STRING, str.toString());
      }
      break;
      case Token::ABSTRACT_TYPE:
      ret = d_state.mkAbstractType();
      break;
      case Token::TYPE:
      ret = d_state.mkType();
      break;
      case Token::BOOL_TYPE:
      ret = d_state.mkBoolType();
      break;
      case Token::UNTERMINATED_QUOTED_SYMBOL:
        d_lex.parseError("Expected SMT-LIBv2 term", true);
        break;
      default:
        d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 term");
        break;
    }

    // Based on the current context, setup next parsed term.
    // We do this only if a context is allocated (!tstack.empty()) and we
    // either just finished parsing a term (!ret.isNull()), or otherwise have
    // indicated that we need to update the context (needsUpdateCtx).
    while (!pstack.empty() && (!ret.isNull() || needsUpdateCtx))
    {
      needsUpdateCtx = false;
      StackFrame& sf = pstack.back();
      switch (sf.d_ctx)
      {
        // ------------------------- argument lists
        case ParseCtx::NEXT_ARG:
        {
          Assert(!ret.isNull());
          // add it to the list of arguments and clear
          sf.d_args.push_back(ret);
          ret = d_null;
        }
        break;
        // ------------------------- let terms
        case ParseCtx::LET_NEXT_BIND:
        {
          // if we parsed a term, process it as a binding
          if (!ret.isNull())
          {
            Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Expr>>& bs = letBinders.back();
            // add binding from the symbol to ret
            Assert(!bs.empty());
            bs.back().second = ret;
            ret = d_null;
            // close the current binding
            d_lex.eatToken(Token::RPAREN);
          }
          else
          {
            // eat the opening left parenthesis of the binding list
            d_lex.eatToken(Token::LPAREN);
          }
          // see if there is another binding
          if (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
          {
            // (, another binding: setup parsing the next term
            // get the symbol and store in the ParseOp
            std::string name = parseSymbol();
            std::vector<std::pair<std::string, Expr>>& bs = letBinders.back();
            bs.emplace_back(name, Expr());
          }
          else
          {
            // ), we are now looking for the body of the let
            sf.d_ctx = ParseCtx::LET_BODY;
            sf.d_nscopes++;
            // push scope
            d_state.pushScope();
            // implement the bindings
            Assert(!letBinders.empty());
            std::vector<std::pair<std::string, Expr>>& bs =
                letBinders.back();
            for (std::pair<std::string, Expr>& b : bs)
            {
              bind(b.first, b.second);
            }
            // done with the binders
            letBinders.pop_back();
          }
        }
        break;
        case ParseCtx::LET_BODY:
        {
          // the let body is the returned term
          d_lex.eatToken(Token::RPAREN);
          sf.pop(d_state);
          pstack.pop_back();
        }
        break;
        // ------------------------- annotated terms
        case ParseCtx::TERM_ANNOTATE_BODY:
        {
          // now parse attribute list
          AttrMap attrs;
          bool pushedScope = false;
          // NOTE parsing attributes may trigger recursive calls to this
          // method.
          parseAttributeList(Kind::NONE, ret, attrs, pushedScope);
          // the scope of the variable is one level up
          if (pushedScope && pstack.size()>1)
          {
            pstack[pstack.size()-2].d_nscopes++;
          }
          // process the attributes
          for (std::pair<const Attr, std::vector<Expr>>& a : attrs)
          {
            switch(a.first)
            {
              case Attr::VAR:
                Assert (a.second.size()==1);
                // it is now (Quote v) for that variable
                ret = d_state.mkQuoteType(a.second[0]);
                break;
              case Attr::IMPLICIT:
                // the term will not be added as an argument to the parent
                // note this always comes after VAR due to enum order
                ret = d_null;
                break;
              case Attr::REQUIRES:
                if (ret.isNull())
                {
                  d_lex.parseError("Cannot mark requires on implicit argument");
                }
                ret = d_state.mkRequires(a.second, ret);
                break;
              case Attr::OPAQUE:
                if (ret.isNull())
                {
                  d_lex.parseError("Cannot mark opaque on implicit argument");
                }
                if (ret.getKind()==Kind::EVAL_REQUIRES)
                {
                  d_lex.parseError("Cannot combine opaque and requires");
                }
                ret = d_state.mkExpr(Kind::OPAQUE_TYPE, {ret});
                break;
              default:
                // ignored
                std::stringstream ss;
                ss << "Unprocessed attribute " << a.first;
                d_lex.warning(ss.str());
                break;
            }
          }
          d_lex.eatToken(Token::RPAREN);
          // finished parsing attributes, ret is either nullptr if implicit,
          // or the term we parsed as the body of the annotation.
          sf.pop(d_state);
          pstack.pop_back();
        }
        break;
        // ------------------------- match terms
        case ParseCtx::MATCH_HEAD:
        {
          Assert(!ret.isNull());
          // add the head
          sf.d_args.push_back(ret);
          ret = d_null;
          d_lex.eatToken(Token::LPAREN);
          // we now parse a pattern
          sf.d_ctx = ParseCtx::MATCH_NEXT_CASE;
          needsUpdateCtx = true;
        }
        break;
        case ParseCtx::MATCH_NEXT_CASE:
        {
          std::vector<Expr>& args = sf.d_args;
          bool checkNextPat = true;
          if (!ret.isNull())
          {
            // if we just got done parsing a term (either a pattern or a return)
            Expr last = args.back();
            if (args.size() > 2 && last.getKind() != Kind::TUPLE)
            {
              // case where we just read a return value
              // replace the back of this with a pair
              args.back() = d_state.mkPair(last, ret);
              d_lex.eatToken(Token::RPAREN);
            }
            else
            {
              // case where we just read a pattern
              args.push_back(ret);
              checkNextPat = false;
            }
            ret = d_null;
          }
          // if no more cases, we are done
          if (checkNextPat)
          {
            if (d_lex.eatTokenChoice(Token::RPAREN, Token::LPAREN))
            {
              d_lex.eatToken(Token::RPAREN);
              Trace("parser") << "Parsed match " << args << std::endl;
              // make a program
              if (args.size()<=2)
              {
                d_lex.parseError("Expected non-empty list of cases");
              }
              Expr atype = d_state.mkAbstractType();
              // environment is the variable list
              std::vector<Expr> vl;
              for (size_t i = 0, nchildren = args[0].getNumChildren();
                   i < nchildren;
                   i++)
              {
                vl.push_back(args[0][i]);
              }
              Expr hd = args[1];
              std::vector<Expr> caseArgs(args.begin()+2, args.end());
              std::vector<Expr> allVars = Expr::getVariables(caseArgs);
              std::vector<Expr> env;
              std::vector<Expr> fargTypes;
              fargTypes.push_back(atype);
              for (const Expr& v : allVars)
              {
                if (std::find(vl.begin(), vl.end(), v)==vl.end())
                {
                  // A variable not appearing in the local binding of the match,
                  // add it to the environment.
                  env.push_back(v);
                  // It will be an argument to the internal program
                  fargTypes.push_back(atype);
                }
              }
              Trace("parser") << "Binder is " << vl << std::endl;
              Trace("parser") << "Env is " << env << std::endl;
              // make the program variable, whose type is abstract
              Expr ftype = d_state.mkFunctionType(fargTypes, atype, false);
              std::stringstream pvname;
              pvname << "_match_" << hd;
              Expr pv = d_state.mkSymbol(Kind::PROGRAM_CONST, pvname.str(), ftype);
              // process the cases
              std::vector<Expr> cases;
              for (size_t i=0, nargs = caseArgs.size(); i<nargs; i++)
              {
                const Expr& cs = caseArgs[i];
                Assert(cs.getKind() == Kind::TUPLE);
                const Expr& lhs = cs[0];
                // check that variables in the pattern are only from the binder
                ensureBound(lhs, vl);
                const Expr& rhs = cs[1];
                std::vector<Expr> appArgs{pv, lhs};
                appArgs.insert(appArgs.end(), env.begin(), env.end());
                Expr lhsa = d_state.mkExpr(Kind::APPLY, appArgs);
                cases.push_back(d_state.mkPair(lhsa, rhs));
                // check free variable requirement
                std::vector<Expr> bvsl = Expr::getVariables(lhs);
                std::vector<Expr> bvsr = Expr::getVariables(rhs);
                for (const Expr& v : bvsr)
                {
                  // if not in the locally bound variable list, skip
                  if (std::find(vl.begin(), vl.end(), v)==vl.end())
                  {
                    continue;
                  }
                  // otherwise, must be in the left hand side
                  if (std::find(bvsl.begin(), bvsl.end(), v)==bvsl.end())
                  {
                    std::stringstream msg;
                    msg << "Unexpected free parameter in match case:" << std::endl;
                    msg << "       Expression: " << rhs << std::endl;
                    msg << "   Free parameter: " << v << std::endl;
                    msg << "Does not occur in: " << lhs << std::endl;
                    d_lex.parseError(msg.str());
                  }
                }
              }
              Expr prog = d_state.mkExpr(Kind::PROGRAM, cases);
              d_state.defineProgram(pv, prog);
              std::vector<Expr> appArgs{pv, hd};
              appArgs.insert(appArgs.end(), env.begin(), env.end());
              ret = d_state.mkExpr(Kind::APPLY, appArgs);
              // pop the stack
              sf.pop(d_state);
              pstack.pop_back();
            }
          }
          // otherwise, ready to parse the next expression
        }
        break;
        default: break;
      }
    }
    // otherwise ret will be returned
  } while (!pstack.empty());
  return ret;
}

Expr ExprParser::parseType()
{
  Expr e = parseExpr();
  // ensure it is a type
  typeCheck(e, d_state.mkType());
  // should not contain stuck term
  if (e.isGround() && e.isEvaluatable())
  {
    std::stringstream msg;
    msg << "Parsed type has an unevalated term:" << std::endl;
    msg << "Type: " << e << std::endl;
    d_lex.parseError(msg.str());
  }
  return e;
}

Expr ExprParser::parseFormula()
{
  Expr e = parseExpr();
  // ensure it has type Bool
  typeCheck(e, d_state.mkBoolType());
  return e;
  
}

std::vector<Expr> ExprParser::parseExprList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    Expr t = parseExpr();
    terms.push_back(t);
    tok = d_lex.nextToken();
  }
  return terms;
}

std::vector<Expr> ExprParser::parseTypeList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    Expr t = parseType();
    terms.push_back(t);
    tok = d_lex.nextToken();
  }
  return terms;
}

Expr ExprParser::parseExprPair()
{
  d_lex.eatToken(Token::LPAREN);
  Expr t1 = parseExpr();
  Expr t2 = parseExpr();
  d_lex.eatToken(Token::RPAREN);
  return d_state.mkPair(t1, t2);
}

std::string ExprParser::parseSymbolicExpr()
{
  std::stringstream ss;
  size_t nparen = 0;
  Token tok;
  do
  {
    tok = d_lex.nextToken();
    switch (tok)
    {
      case Token::LPAREN: nparen++; break;
      case Token::RPAREN: nparen--; break;
      case Token::EOF_TOK:
      {
        d_lex.parseError("Expected s-expression");
      }
      break;
      default: break;
    }
    ss << d_lex.tokenStr() << " ";
  }while (nparen!=0);
  return ss.str();
}

std::vector<Expr> ExprParser::parseExprPairList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<Expr> terms;
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    Expr t1 = parseExpr();
    Expr t2 = parseExpr();
    Expr t = d_state.mkPair(t1, t2);
    terms.push_back(t);
    d_lex.eatToken(Token::RPAREN);
  }
  return terms;
}

std::vector<Expr> ExprParser::parseAndBindSortedVarList(bool isLookup)
{
  std::vector<Expr> impls;
  return parseAndBindSortedVarList(impls, isLookup);
}

std::vector<Expr> ExprParser::parseAndBindSortedVarList(
                     std::vector<Expr>& impls, bool isLookup)
{
  std::vector<Expr> varList;
  d_lex.eatToken(Token::LPAREN);
  std::string name;
  Expr t;
  Attr ck = Attr::NONE;
  Expr cons;
  // while the next token is LPAREN, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    name = parseSymbol();
    t = parseType();
    Expr v;
    bool isImplicit = false;
    if (isLookup)
    {
      // lookup and type check
      v = d_state.getBoundVar(name, t);
      // bind it for now
      bind(name, v);
    }
    else
    {
      v = d_state.mkSymbol(Kind::PARAM, name, t);
      bind(name, v);
      // parse attribute list
      AttrMap attrs;
      parseAttributeList(Kind::PARAM, v, attrs);
      if (attrs.find(Attr::IMPLICIT)!=attrs.end())
      {
        attrs.erase(Attr::IMPLICIT);
        isImplicit = true;
        impls.push_back(v);
      }
      // process the attribute map, which may mark the parameter as a list
      processAttributeMap(attrs, ck, cons, {});
      if (ck!=Attr::NONE)
      {
        d_state.markConstructorKind(v, ck, cons);
        ck = Attr::NONE;
        cons = d_null;
      }
    }
    d_lex.eatToken(Token::RPAREN);
    if (!isImplicit)
    {
      varList.push_back(v);
    }
  }
  return varList;
}

std::vector<std::pair<Expr, Expr>> ExprParser::parseAndBindLetList()
{
  std::vector<std::pair<Expr, Expr>> letList;
  d_lex.eatToken(Token::LPAREN);
  std::string name;
  Expr v, t, tt;
  // while the next token is LPAREN, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    name = parseSymbol();
    t = parseExpr();
    d_lex.eatToken(Token::RPAREN);
    tt = typeCheck(t);
    v = d_state.mkSymbol(Kind::VARIABLE, name, tt);
    letList.emplace_back(v, t);
  }
  // now perform the bindings, which bind to the variable, not its definition
  for (std::pair<Expr, Expr>& ll : letList)
  {
    bind(ll.first.getSymbol(), ll.first);
  }
  return letList;
}

std::string ExprParser::parseSymbol()
{
  Token tok = d_lex.nextToken();
  return tokenStrToSymbol(tok);
}

std::vector<std::string> ExprParser::parseSymbolList()
{
  d_lex.eatToken(Token::LPAREN);
  std::vector<std::string> symbols;
  Token tok = d_lex.nextToken();
  while (tok != Token::RPAREN)
  {
    d_lex.reinsertToken(tok);
    std::string sym = parseSymbol();
    symbols.push_back(sym);
    tok = d_lex.nextToken();
  }
  return symbols;
}

bool ExprParser::parseDatatypesDef(
    const std::vector<std::string>& dnames,
    const std::vector<size_t>& arities,
    std::map<const ExprValue*, std::vector<Expr>>& dts,
    std::map<const ExprValue*, std::vector<Expr>>& dtcons,
    std::unordered_set<const ExprValue*>& ambCons)
{
  Assert(dnames.size() == arities.size()
         || (dnames.size() == 1 && arities.empty()));
  // Declare the datatypes that are currently being defined as unresolved
  // types. If we do not know the arity of the datatype yet, we wait to
  // define it until parsing the preamble of its body, which may optionally
  // involve `par`. This is limited to the case of single datatypes defined
  // via declare-datatype, and hence no datatype body is parsed without
  // having all types declared. This ensures we can parse datatypes with
  // nested recursion, e.g. datatypes D having a subfield type
  // (Array Int D).
  std::vector<Expr> dtlist;
  for (unsigned i = 0, dsize = dnames.size(); i < dsize; i++)
  {
    if (i >= arities.size())
    {
      // do not know the arity yet
      continue;
    }
    // make the datatype, which has the given arity
    Expr t = d_state.mkTypeConstant(dnames[i], arities[i]);
    // bind
    if (!d_state.bind(dnames[i], t))
    {
      return false;
    }
    dtlist.push_back(t);
  }
  // while we get another datatype declaration, or close the list
  Token tok = d_lex.nextToken();
  size_t i = 0;
  while (tok == Token::LPAREN)
  {
    std::vector<Expr> params;
    if (i >= dnames.size())
    {
      d_lex.parseError("Too many datatypes defined in this block.");
    }
    tok = d_lex.nextToken();
    bool pushedScope = false;
    if (tok == Token::PAR)
    {
      pushedScope = true;
      d_state.pushScope();
      std::vector<std::string> symList = parseSymbolList();
      if (symList.empty())
      {
        d_lex.parseError("Expected non-empty parameter list");
      }
      // parameters are type variables
      for (const std::string& sym : symList)
      {
        Expr t = d_state.mkSymbol(Kind::PARAM, sym, d_state.mkType());
        if (!d_state.bind(sym, t))
        {
          return false;
        }
        params.push_back(t);
      }
    }
    else
    {
      d_lex.reinsertToken(tok);
      // we will parse the parentheses-enclosed construct list below
      d_lex.reinsertToken(Token::LPAREN);
    }
    if (i >= arities.size())
    {
      // if the arity is not yet fixed, bind it now
      Expr t = d_state.mkTypeConstant(dnames[i], params.size());
      // bind
      if (!d_state.bind(dnames[i], t))
      {
        return false;
      }
      dtlist.push_back(t);
    }
    else if (arities[i] >= 0 && params.size() != arities[i])
    {
      // if the arity was fixed by prelude and is not equal to the number of
      // parameters
      d_lex.parseError("Wrong number of parameters for datatype.");
    }
    // read constructor definition list, populate into the current datatype
    Expr& dt = dtlist[i];
    Expr dti = dt;
    if (!params.empty())
    {
      std::vector<Expr> dapp;
      dapp.push_back(dt);
      dapp.insert(dapp.end(), params.begin(), params.end());
      dti = d_state.mkExpr(Kind::APPLY, dapp);
    }
    std::vector<std::pair<std::string, Expr>> toBind;
    std::vector<Expr>& clist = dts[dt.getValue()];
    parseConstructorDefinitionList(dti, clist, dtcons, toBind, ambCons, params);
    if (pushedScope)
    {
      d_lex.eatToken(Token::RPAREN);
      d_state.popScope();
    }
    for (std::pair<std::string, Expr>& b : toBind)
    {
      if (!d_state.bind(b.first, b.second))
      {
        return false;
      }
    }
    tok = d_lex.nextToken();
    i++;
  }
  if (dtlist.size() != dnames.size())
  {
    d_lex.unexpectedTokenError(tok, "Wrong number of datatypes provided.");
  }
  d_lex.reinsertToken(tok);
  return true;
}

void ExprParser::parseConstructorDefinitionList(
    Expr& dt,
    std::vector<Expr>& conslist,
    std::map<const ExprValue*, std::vector<Expr>>& dtcons,
    std::vector<std::pair<std::string, Expr>>& toBind,
    std::unordered_set<const ExprValue*>& ambCons,
    const std::vector<Expr>& params)
{
  d_lex.eatToken(Token::LPAREN);
  Expr boolType = d_state.mkBoolType();
  // parse another constructor or close the list
  while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
  {
    std::string name = parseSymbol();
    std::vector<Expr> typelist;
    std::vector<Expr> sels;
    // parse another selector or close the current constructor
    while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
    {
      std::string id = parseSymbol();
      Expr t = parseType();
      typelist.push_back(t);
      Expr stype = d_state.mkFunctionType({dt}, t);
      Expr sel = d_state.mkSymbol(Kind::CONST, id, stype);
      toBind.emplace_back(id,sel);
      sels.push_back(sel);
      std::stringstream ss;
      ss << "update-" << id;
      Expr utype = d_state.mkFunctionType({dt, t}, dt);
      Expr updater = d_state.mkSymbol(Kind::CONST, ss.str(), utype);
      toBind.emplace_back(ss.str(), updater);
      d_lex.eatToken(Token::RPAREN);
    }
    bool isAmb = false;
    if (!params.empty())
    {
      // if this is an ambiguous datatype constructor, we add (Quote T)
      // as the first argument type.
      Expr tup = d_state.mkExpr(Kind::TUPLE, typelist);
      std::vector<Expr> pargs = Expr::getVariables(tup);
      Expr fv = findFreeVar(dt, pargs);
      Trace("param-dt") << "Parameteric datatype constructor: " << name;
      Trace("param-dt") << (fv.isNull() ? " un" : " ") << "ambiguous"
                        << std::endl;
      if (!fv.isNull())
      {
        Expr odt = d_state.mkQuoteType(dt);
        typelist.insert(typelist.begin(), odt);
        isAmb = true;
      }
    }
    Expr ctype = d_state.mkFunctionType(typelist, dt);
    Expr cons = d_state.mkSymbol(Kind::CONST, name, ctype);
    toBind.emplace_back(name, cons);
    conslist.push_back(cons);
    // make the discriminator
    std::stringstream ss;
    ss << "is-" << name;
    Expr dtype = d_state.mkFunctionType({dt}, boolType);
    Expr tester = d_state.mkSymbol(Kind::CONST, ss.str(), dtype);
    toBind.emplace_back(ss.str(), tester);
    dtcons[cons.getValue()] = sels;
    if (isAmb)
    {
      ambCons.insert(cons.getValue());
    }
  }
}

std::string ExprParser::parseKeyword()
{
  d_lex.eatToken(Token::KEYWORD);
  std::string s = d_lex.tokenStr();
  // strip off the initial colon
  return s.erase(0, 1);
}

uint32_t ExprParser::parseIntegerNumeral()
{
  d_lex.eatToken(Token::INTEGER_LITERAL);
  return tokenStrToUnsigned();
}

uint32_t ExprParser::tokenStrToUnsigned()
{
  // forbid leading zeroes?
  std::string token = d_lex.tokenStr();
  if (token.size() > 1 && token[0] == '0')
  {
    d_lex.parseError("Numeral with leading zeroes are forbidden");
  }
  uint32_t result;
  std::stringstream ss;
  ss << d_lex.tokenStr();
  ss >> result;
  return result;
}

std::string ExprParser::tokenStrToSymbol(Token tok)
{
  std::string id;
  switch (tok)
  {
    case Token::SYMBOL: id = d_lex.tokenStr(); break;
    case Token::QUOTED_SYMBOL:
      id = d_lex.tokenStr();
      // strip off the quotes
      id = id.erase(0, 1);
      id = id.erase(id.size() - 1, 1);
      break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      d_lex.parseError("Expected SMT-LIBv2 symbol", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected SMT-LIBv2 symbol");
      break;
  }
  return id;
}

std::string ExprParser::parseStr(bool unescape)
{
  d_lex.eatToken(Token::STRING_LITERAL);
  std::string s = d_lex.tokenStr();
  if (unescape)
  {
    unescapeString(s);
  }
  return s;
}

void ExprParser::parseAttributeList(Kind k, Expr& e, AttrMap& attrs, bool& pushedScope)
{
  std::map<std::string, Attr>::iterator its;
  // while the next token is KEYWORD, exit if RPAREN
  while (d_lex.eatTokenChoice(Token::KEYWORD, Token::RPAREN))
  {
    std::string key = d_lex.tokenStr();
    its = d_strToAttr.find(key);
    Expr val;
    if (its==d_strToAttr.end())
    {
      // parse and skip value if it exists
      Token tok = d_lex.peekToken();
      if (tok!=Token::KEYWORD && tok!=Token::RPAREN)
      {
        parseSymbolicExpr();
      }
      // store dummy, to mark that we read an attribute
      Warning() << "Unsupported attribute " << key << std::endl;
      attrs[Attr::NONE].push_back(val);
      continue;
    }
    Attr a = its->second;
    bool handled = false;
    // split on the context of the attribute, as given by a kind
    switch (k)
    {
      case Kind::PROOF_RULE:
      {
        // attributes on declare-rule
        if (a==Attr::SORRY)
        {
          handled = true;
          d_state.markProofRuleSorry(e.getValue());
        }
      }
        break;
      case Kind::PARAM:
      {
        // attributes on parameters
        if (a==Attr::LIST || a==Attr::IMPLICIT)
        {
          handled = true;
        }
      }
        break;
      case Kind::CONST:
      {
        // attributes on declare-const
        switch (a)
        {
          case Attr::RIGHT_ASSOC:
          case Attr::LEFT_ASSOC:
            // requires no value
            handled = true;
            break;
          case Attr::RIGHT_ASSOC_NIL:
          case Attr::LEFT_ASSOC_NIL:
          case Attr::CHAINABLE:
          case Attr::PAIRWISE:
          case Attr::BINDER:
          {
            // requires an expression that follows
            handled = true;
            val = parseExpr();
          }
            break;
          case Attr::LET_BINDER:
          {
            // requires an expression pair that follows
            handled = true;
            val = parseExprPair();
          }
            break;
          default:break;
        }
      }
        break;
      case Kind::LAMBDA:
      {
        // only :type is available in define
        if (a==Attr::TYPE)
        {
          Assert (!e.isNull());
          handled = true;
          val = parseExpr();
          // run type checking
          typeCheck(e, val);
        }
      }
        break;
      case Kind::NONE:
      {
        // attributes on general terms, including type arguments
        handled = true;
        switch (a)
        {
          case Attr::IMPLICIT:
          case Attr::OPAQUE:
            // requires no value
            break;
          case Attr::VAR:
          {
            if (e.isNull())
            {
              d_lex.parseError("Cannot use :var in this context");
            }
            if (attrs.find(Attr::VAR)!=attrs.end())
            {
              d_lex.parseError("Cannot use :var on the same term more than once");
            }
            std::string name = parseSymbol();
            // e should be a type
            val = d_state.mkSymbol(Kind::PARAM, name, e);
            // immediately bind
            if (!pushedScope)
            {
              pushedScope = true;
              d_state.pushScope();
            }
            bind(name, val);
          }
          break;
          case Attr::RESTRICT:
          {
            // requires an expression that follows
            val = parseExpr();
          }
            break;
          case Attr::REQUIRES:
          {
            // requires a pair
            val = parseExprPair();
          }
            break;
          case Attr::SYNTAX:
          {
            // ignores the literal kind
            parseLiteralKind();
          }
            break;
          default:
            handled = false;
            break;
        }
      }
        break;
      default:
        break;
    }
    if (!handled)
    {
      d_lex.parseError("Unhandled attribute " + key);
    }
    attrs[its->second].push_back(val);
  }
  d_lex.reinsertToken(Token::RPAREN);
}

void ExprParser::parseAttributeList(Kind k, Expr& e, AttrMap& attrs)
{
  bool pushedScope = false;
  parseAttributeList(k, e, attrs, pushedScope);
  // pop the scope if necessary
  if (pushedScope)
  {
    d_state.popScope();
  }
}

Kind ExprParser::parseLiteralKind()
{
  std::string name = parseSymbol();
  std::map<std::string, Kind>::iterator it = d_strToLiteralKind.find(name);
  if (it==d_strToLiteralKind.end())
  {
    std::stringstream ss;
    ss << "Unknown literal kind " << name;
    d_lex.parseError(ss.str());
  }
  return it->second;
}

void ExprParser::unescapeString(std::string& s)
{
  // strip off the quotes
  s = s.erase(0, 1);
  s = s.erase(s.size() - 1, 1);
  for (size_t i = 0, ssize = s.size(); i < ssize; i++)
  {
    if ((unsigned)s[i] > 127 && !isprint(s[i]))
    {
      d_lex.parseError(
          "Extended/unprintable characters are not "
          "part of SMT-LIB, and they must be encoded "
          "as escape sequences");
    }
  }
  size_t dst = 0;
  for (size_t src = 0; src<s.size(); ++src, ++dst)
  {
    s[dst] = s[src];
    if (s[src]=='"')
    {
      ++src;
    }
  }
  s.erase(dst);
}

Expr ExprParser::getVar(const std::string& name)
{
  Expr ret = d_state.getVar(name);
  if (ret.isNull())
  {
    std::stringstream ss;
    ss << "Could not find symbol " << name;
    d_lex.parseError(ss.str());
  }
  return ret;
}

Expr ExprParser::getProofRule(const std::string& name)
{
  Expr v = d_state.getProofRule(name);
  if (v.isNull())
  {
    std::stringstream ss;
    ss << "Could not find proof rule " << name;
    d_lex.parseError(ss.str());
  }
  if (v.getKind() != Kind::PROOF_RULE)
  {
    std::stringstream ss;
    ss << "Expected proof rule for " << name;
    d_lex.parseError(ss.str());
  }
  return v;
}

void ExprParser::bind(const std::string& name, Expr& e)
{
  if (!d_state.bind(name, e))
  {
    std::stringstream ss;
    ss << "Failed to bind symbol " << name
       << ", since the symbol has already been defined";
    d_lex.parseError(ss.str());
  }
}

Expr ExprParser::typeCheck(Expr& e)
{
  // type check immediately
  const Expr& v = d_state.getTypeChecker().getType(e);
  if (v.isNull())
  {
    // we allocate stringstream for error messages only when an error occurs
    // thus, we require recomputing the error message here.
    std::stringstream ss;
    d_state.getTypeChecker().getType(e, &ss);
    std::stringstream msg;
    msg << "Type checking failed:" << std::endl;
    msg << "Expression: " << e << std::endl;
    msg << "Message: " << ss.str() << std::endl;
    d_lex.parseError(msg.str());
  }
  return v;
}
Expr ExprParser::typeCheckApp(std::vector<Expr>& children)
{
  // ensure all children are type checked
  for (Expr& c : children)
  {
    typeCheck(c);
  }
  const Expr& v = d_state.getTypeChecker().getTypeApp(children);
  if (v.isNull())
  {
    // we allocate stringstream for error messages only when an error occurs
    // thus, we require recomputing the error message here.
    std::stringstream ss;
    d_state.getTypeChecker().getTypeApp(children, &ss);
    std::stringstream msg;
    msg << "Type checking application failed when applying " << children[0]
        << std::endl;
    msg << "Children: "
        << std::vector<Expr>(children.begin() + 1, children.end()) << std::endl;
    msg << "Message: " << ss.str() << std::endl;
    d_lex.parseError(msg.str());
  }
  return v;
}

Expr ExprParser::typeCheck(Expr& e, const Expr& expected)
{
  Expr et = typeCheck(e);
  if (et!=expected)
  {
    std::stringstream msg;
    msg << "Expression of unexpected type:" << std::endl;
    msg << "Expression: " << e << std::endl;
    msg << "      Type: " << et << std::endl;
    msg << "  Expected: " << expected << std::endl;
    d_lex.parseError(msg.str());
  }
  return et;
}

Expr ExprParser::findFreeVar(const Expr& e, const std::vector<Expr>& bvs)
{
  std::vector<Expr> efv = Expr::getVariables(e);
  for (const Expr& v : efv)
  {
    if (std::find(bvs.begin(), bvs.end(), v)==bvs.end())
    {
      // ignore distinguished variables
      if (v==d_state.mkConclusion() || v==d_state.mkSelf())
      {
        continue;
      }
      return v;
    }
  }
  return d_null;
}

void ExprParser::ensureBound(const Expr& e, const std::vector<Expr>& bvs)
{
  Expr v = findFreeVar(e, bvs);
  if (!v.isNull())
  {
    std::stringstream msg;
    msg << "Unexpected free parameter in expression:" << std::endl;
    msg << "      Expression: " << e << std::endl;
    msg << "  Free parameter: " << v << std::endl;
    msg << "Bound parameters: " << bvs << std::endl;
    d_lex.parseError(msg.str());
  }
}

void ExprParser::processAttributeMap(const AttrMap& attrs,
                                     Attr& ck,
                                     Expr& cons,
                                     const std::vector<Expr>& params)
{
  ck = Attr::NONE;
  for (const std::pair<const Attr, std::vector<Expr>>& a : attrs)
  {
    for (const Expr& av : a.second)
    {
      if (isConstructorKindAttr(a.first))
      {
        if (ck!=Attr::NONE)
        {
          std::stringstream ss;
          ss << "Cannot set multiple constructor types ";
          ss << "(" << ck << " and " << a.first << ")" << std::endl;
          d_lex.warning(ss.str());
          continue;
        }
        // it specifies how to construct terms involving this term
        // if the constructor spec is non-ground, make a lambda
        if (!av.isNull() && !av.isGround())
        {
          Assert (!params.empty());
          cons = d_state.mkParameterized(av.getValue(), params);
        }
        else
        {
          cons = av;
          // if the nil constructor doesn't use parameters, just ignore
          if (!params.empty())
          {
            Warning() << "Ignoring unused parameters for definition of "
                      << "symbol with nil constructor " << av << std::endl;
          }
        }
        ck = a.first;
      }
      else
      {
        std::stringstream ss;
        ss << "Unhandled attribute " << a.first << std::endl;
        d_lex.warning(ss.str());
      }
    }
  }
}

}  // namespace ethos
