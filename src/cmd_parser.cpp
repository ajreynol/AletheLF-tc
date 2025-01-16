/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************
 *
 * The smt2 command parser.
 */

#include "cmd_parser.h"

#include <iostream>
#include <ostream>
#include "base/output.h"

namespace ethos {

CmdParser::CmdParser(Lexer& lex,
                     State& state,
                     ExprParser& eparser,
                     bool isReference)
    : d_lex(lex), d_state(state), d_sts(state.getStats()),
      d_eparser(eparser), d_isReference(isReference), d_isFinished(false)
{
  // initialize the command tokens
  // commands supported in both inputs and proofs
  d_table["declare-codatatype"] = Token::DECLARE_CODATATYPE;    // undocumented, TODO: remove
  d_table["declare-codatatypes"] = Token::DECLARE_CODATATYPES;  // undocumented, TODO: remove
  d_table["declare-const"] = Token::DECLARE_CONST;
  d_table["declare-datatype"] = Token::DECLARE_DATATYPE;
  d_table["declare-datatypes"] = Token::DECLARE_DATATYPES;
  d_table["echo"] = Token::ECHO;
  d_table["exit"] = Token::EXIT;
  d_table["set-option"] = Token::SET_OPTION;
  d_table["pop"] = Token::POP;    // undocumented
  d_table["push"] = Token::PUSH;  // undocumented
  d_table["reset"] = Token::RESET;

  if (d_isReference)
  {
    // only used in smt2 queries
    d_table["assert"] = Token::ASSERT;
    d_table["declare-fun"] = Token::DECLARE_FUN;
    d_table["declare-sort"] = Token::DECLARE_SORT;
    d_table["define-const"] = Token::DEFINE_CONST;
    d_table["define-fun"] = Token::DEFINE_FUN;
    d_table["define-sort"] = Token::DEFINE_SORT;
    d_table["check-sat"] = Token::CHECK_SAT;
    d_table["check-sat-assuming"] = Token::CHECK_SAT_ASSUMING;
    d_table["set-logic"] = Token::SET_LOGIC;
    d_table["set-info"] = Token::SET_INFO;
  }
  else
  {
    d_table["assume"] = Token::ASSUME;
    d_table["assume-push"] = Token::ASSUME_PUSH;
    d_table["declare-consts"] = Token::DECLARE_CONSTS;
    d_table["declare-oracle-fun"] = Token::DECLARE_ORACLE_FUN;
    d_table["declare-parameterized-const"] = Token::DECLARE_PARAMETERIZED_CONST;
    d_table["declare-rule"] = Token::DECLARE_RULE;
    d_table["declare-type"] = Token::DECLARE_TYPE;
    d_table["define"] = Token::DEFINE;
    d_table["define-type"] = Token::DEFINE_TYPE;
    d_table["include"] = Token::INCLUDE;
    d_table["program"] = Token::PROGRAM;
    d_table["reference"] = Token::REFERENCE;
    d_table["step"] = Token::STEP;
    d_table["step-pop"] = Token::STEP_POP;
  }
  
  d_statsEnabled = d_state.getOptions().d_stats;
}

Token CmdParser::nextCommandToken()
{
  Token tok = d_lex.nextToken();
  // symbols as commands
  if (tok == Token::SYMBOL)
  {
    std::string str(d_lex.tokenStr());
    std::map<std::string, Token>::iterator it = d_table.find(str);
    if (it != d_table.end())
    {
      return it->second;
    }
  }
  return tok;
}

bool CmdParser::parseNextCommand()
{
  // if we are at the end of file, return the null command
  if (d_isFinished || d_lex.eatTokenChoice(Token::EOF_TOK, Token::LPAREN))
  {
    return false;
  }
  Token tok = nextCommandToken();
  switch (tok)
  {
    // (assume <symbol> <term>)
    // (push <symbol> <term>)
    case Token::ASSUME:
    case Token::ASSUME_PUSH:
    {
      if (tok==Token::ASSUME_PUSH)
      {
        d_state.pushAssumptionScope();
      }
      std::string name = d_eparser.parseSymbol();
      // parse what is proven
      Expr proven = d_eparser.parseFormula();
      Expr pt = d_state.mkProofType(proven);
      Expr v = d_state.mkSymbol(Kind::CONST, name, pt);
      d_eparser.bind(name, v);
      if (!d_state.addAssumption(proven))
      {
        std::stringstream ss;
        ss << "The assumption " << name << " was not part of the referenced assertions";
        d_lex.parseError(ss.str());
      }
    }
    break;
    // (declare-fun <symbol> (<sort>∗) <sort>)
    // (declare-oracle-fun <symbol> (<sort>∗) <sort>)
    // (declare-const <symbol> <sort>)
    // (declare-parameterized-const (<sorted_var>*) <symbol> <sort>)
    case Token::DECLARE_CONST:
    case Token::DECLARE_FUN:
    case Token::DECLARE_PARAMETERIZED_CONST:
    case Token::DECLARE_ORACLE_FUN:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> sorts;
      std::vector<Expr> params;
      bool flattenFunction = (tok != Token::DECLARE_ORACLE_FUN);
      if (tok == Token::DECLARE_FUN || tok == Token::DECLARE_ORACLE_FUN)
      {
        sorts = d_eparser.parseTypeList();
      }
      else if (tok == Token::DECLARE_PARAMETERIZED_CONST)
      {
        d_state.pushScope();
        params = d_eparser.parseAndBindSortedVarList();
      }
      Expr ret = d_eparser.parseType();
      Attr ck = Attr::NONE;
      Expr cons;
      Kind sk;
      Expr t;
      sk = Kind::CONST;
      if (tok==Token::DECLARE_ORACLE_FUN)
      {
        ck = Attr::ORACLE;
        sk = Kind::ORACLE;
        std::string oname = d_eparser.parseSymbol();
        cons = d_state.mkLiteral(Kind::STRING, oname);
        // don't permit attributes for oracle functions
      }
      else if (tok==Token::DECLARE_CONST || tok==Token::DECLARE_PARAMETERIZED_CONST)
      {
        // possible attribute list
        AttrMap attrs;
        d_eparser.parseAttributeList(Kind::CONST, t, attrs);
        // determine if an attribute specified a constructor kind
        d_eparser.processAttributeMap(attrs, ck, cons, params);
      }
      // declare-fun does not parse attribute list, as it is only in smt2
      t = ret;
      if (!sorts.empty())
      {
        t = d_state.mkFunctionType(sorts, ret, flattenFunction);
      }
      std::vector<Expr> opaqueArgs;
      while (t.getKind()==Kind::FUNCTION_TYPE && t[0].getKind()==Kind::OPAQUE_TYPE)
      {
        Assert (t.getNumChildren()==2);
        Assert (t[0].getNumChildren()==1);
        opaqueArgs.push_back(t[0][0]);
        t = t[1];
      }
      if (!opaqueArgs.empty())
      {
        if (ck!=Attr::NONE)
        {
          d_lex.parseError("Can only use opaque argument on functions without attributes.");
        }
        // Reconstruct with opaque arguments, do not flatten function type.
        t = d_state.mkFunctionType(opaqueArgs, t, false);
        ck = Attr::OPAQUE;
      }
      Expr v;
      if (sk==Kind::VARIABLE)
      {
        // We get the canonical variable, not a fresh one. This ensures that
        // globally defined variables coincide with those that appear in
        // binders when applicable.
        v = d_state.getBoundVar(name, t);
      }
      else
      {
        v = d_state.mkSymbol(sk, name, t);
      }
      // if the type has a property, we mark it on the variable of this type
      if (ck!=Attr::NONE)
      {
        if (!d_state.markConstructorKind(v, ck, cons))
        {
          std::stringstream ss;
          ss << "Failed to mark " << v << " with attribute " << ck;
          d_lex.parseError(ss.str());
        }
      }
      // pop the scope
      if (tok == Token::DECLARE_PARAMETERIZED_CONST)
      {
        d_state.popScope();
      }
      // bind
      d_eparser.bind(name, v);
    }
    break;
    // single or multiple datatype
    // (declare-datatype <symbol> <datatype_dec>)
    // (declare-codatatype <symbol> <datatype_dec>)
    // (declare-datatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    // (declare-codatatypes (<sort_dec>^{n+1}) (<datatype_dec>^{n+1}) )
    case Token::DECLARE_CODATATYPE:
    case Token::DECLARE_DATATYPE:
    case Token::DECLARE_CODATATYPES:
    case Token::DECLARE_DATATYPES:
    {
      bool isCo = (tok==Token::DECLARE_CODATATYPES || tok==Token::DECLARE_CODATATYPE);
      bool isMulti = (tok==Token::DECLARE_CODATATYPES || tok==Token::DECLARE_DATATYPES);
      std::vector<std::string> dnames;
      std::vector<size_t> arities;
      std::map<const ExprValue*, std::vector<Expr>> dts;
      std::map<const ExprValue*, std::vector<Expr>> dtcons;
      std::unordered_set<const ExprValue*> ambCons;
      if (isMulti)
      {
        d_lex.eatToken(Token::LPAREN);
        // parse (<sort_dec>^{n+1})
        // while the next token is LPAREN, exit if RPAREN
        while (d_lex.eatTokenChoice(Token::LPAREN, Token::RPAREN))
        {
          std::string name = d_eparser.parseSymbol();
          size_t arity = d_eparser.parseIntegerNumeral();
          dnames.push_back(name);
          arities.push_back(arity);
          d_lex.eatToken(Token::RPAREN);
        }
        if (dnames.empty())
        {
          d_lex.parseError("Empty list of datatypes");
        }
        // parse (<datatype_dec>^{n+1})
        d_lex.eatToken(Token::LPAREN);
      }
      else
      {
        std::string name = d_eparser.parseSymbol();
        dnames.push_back(name);
      }
      if (!d_eparser.parseDatatypesDef(dnames, arities, dts, dtcons, ambCons))
      {
        d_lex.parseError("Failed to bind symbols for datatype definition");
      }
      // mark the attributes
      Attr attr = isCo ? Attr::CODATATYPE : Attr::DATATYPE;
      for (std::pair<const ExprValue* const, std::vector<Expr>>& d : dts)
      {
        Expr dt = Expr(d.first);
        Expr ctuple = d_state.mkList(d.second);
        d_state.markConstructorKind(dt, attr, ctuple);
      }
      for (std::pair<const ExprValue* const, std::vector<Expr>>& c : dtcons)
      {
        // may be ambiguous
        Attr ac = ambCons.find(c.first) != ambCons.end()
                      ? Attr::AMB_DATAYPE_CONSTRUCTOR
                      : Attr::DATATYPE_CONSTRUCTOR;
        Expr cons = Expr(c.first);
        Expr stuple = d_state.mkList(c.second);
        d_state.markConstructorKind(cons, ac, stuple);
      }
      if (isMulti)
      {
        d_lex.eatToken(Token::RPAREN);
      }
    }
    break;
    // (declare-consts <symbol> <sort>)
    case Token::DECLARE_CONSTS:
    {
      Kind k = d_eparser.parseLiteralKind();
      Expr t = d_eparser.parseType();
      // maybe requires?
      // set the type rule
      d_state.setLiteralTypeRule(k, t);
    }
    break;
    // (declare-rule ...)
    case Token::DECLARE_RULE:
    {
      // ensure zero scope
      if (d_state.getAssumptionLevel()>0)
      {
        d_lex.parseError("Rules must be declared at assumption level zero");
      }
      d_state.pushScope();
      std::string name = d_eparser.parseSymbol();
      if (d_lex.peekToken()==Token::KEYWORD)
      {
        std::string keyword = d_eparser.parseKeyword();
        if (keyword!="ethos")
        {
          d_lex.parseError("Unsupported rule format");
        }
      }
      std::vector<Expr> vs =
          d_eparser.parseAndBindSortedVarList();
      Expr assume;
      Expr plCons;
      std::vector<Expr> premises;
      std::vector<Expr> args;
      std::vector<Expr> reqs;
      Expr conc;
      // parse premises, optionally
      std::string keyword = d_eparser.parseKeyword();
      if (keyword=="assumption")
      {
        assume = d_eparser.parseExpr();
        keyword = d_eparser.parseKeyword();
      }
      if (keyword=="premises")
      {
        premises = d_eparser.parseExprList();
        keyword = d_eparser.parseKeyword();
      }
      else if (keyword=="premise-list")
      {
        // :premise-list <pattern> <cons>
        Expr pat = d_eparser.parseExpr();
        plCons = d_eparser.parseExpr();
        // pattern is the single premise
        premises.push_back(pat);
        keyword = d_eparser.parseKeyword();
      }
      // parse args, optionally
      if (keyword=="args")
      {
        args = d_eparser.parseExprList();
        keyword = d_eparser.parseKeyword();
      }
      // parse requirements, optionally
      if (keyword=="requires")
      {
        // we support eo::conclusion in requirements
        d_state.pushScope();
        d_state.bind("eo::conclusion", d_state.mkConclusion());
        // parse the expression pair list
        reqs = d_eparser.parseExprPairList();
        keyword = d_eparser.parseKeyword();
        d_state.popScope();
      }
      // parse conclusion
      if (keyword=="conclusion")
      {
        conc = d_eparser.parseExpr();
      }
      else if (keyword=="conclusion-given")
      {
        // :conclusion-given is equivalent to :conclusion eo::conclusion
        conc = d_state.mkConclusion();
      }
      else
      {
        d_lex.parseError("Expected conclusion in declare-rule");
      }
      std::vector<Expr> argTypes;
      for (Expr& e : args)
      {
        Expr et = d_state.mkQuoteType(e);
        argTypes.push_back(et);
      }
      for (const Expr& e : premises)
      {
        Expr pet = d_state.mkProofType(e);
        argTypes.push_back(pet);
      }
      if (!assume.isNull())
      {
        Expr ast = d_state.mkQuoteType(assume);
        argTypes.push_back(ast);
      }
      Expr ret = d_state.mkProofType(conc);
      // include the requirements into the return type
      if (!reqs.empty())
      {
        ret = d_state.mkRequires(reqs, ret);
      }
      // Ensure all free variables in the conclusion are bound in the arguments.
      // Otherwise, this rule will always generate a free variable, which is
      // likely unintentional.
      std::vector<Expr> bvs = Expr::getVariables(argTypes);
      d_eparser.ensureBound(ret, bvs);
      // make the overall type
      if (!argTypes.empty())
      {
        ret = d_state.mkFunctionType(argTypes, ret, false);
      }
      d_state.popScope();
      Expr rule = d_state.mkSymbol(Kind::PROOF_RULE, name, ret);
      d_eparser.typeCheck(rule);
      d_eparser.bind(name, rule);
      if (!plCons.isNull())
      {
        d_state.markConstructorKind(rule, Attr::PREMISE_LIST, plCons);
      }
      AttrMap attrs;
      d_eparser.parseAttributeList(Kind::PROOF_RULE, rule, attrs);
    }
    break;
    // (declare-sort <symbol> <numeral>)
    case Token::DECLARE_SORT:
    {
      //d_state.checkThatLogicIsSet();
      //d_state.checkLogicAllowsFreeExprs();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      size_t arity = d_eparser.parseIntegerNumeral();
      Expr decType = d_state.mkTypeConstant(name, arity);
      d_eparser.bind(name, decType);
    }
    break;
    // (declare-type <symbol> (<sort>*))
    case Token::DECLARE_TYPE:
    {
      //d_state.checkThatLogicIsSet();
      //d_state.checkLogicAllowsFreeExprs();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> args = d_eparser.parseTypeList();
      Expr type;
      Expr ttype = d_state.mkType();
      if (args.empty())
      {
        type = ttype;
      }
      else
      {
        type = d_state.mkFunctionType(args, ttype);
      }
      Expr decType = d_state.mkSymbol(Kind::CONST, name, type);
      d_eparser.bind(name, decType);
    }
    break;
    // (define-const <symbol> <sort> <term>)
    case Token::DEFINE_CONST:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      Expr ret = d_eparser.parseType();
      Expr e = d_eparser.parseExpr();
      d_eparser.typeCheck(e, ret);
      d_eparser.bind(name, e);
    }
    break;
    // (define-fun <symbol> (<sorted_var>*) <sort> <term>)
    // (define-type <symbol> (<sorted_var>*) <term>)
    // (define <symbol> (<sorted_var>*) <term> <attr>*)
    case Token::DEFINE_FUN:
    case Token::DEFINE_TYPE:
    case Token::DEFINE:
    {
      d_state.pushScope();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> impls;
      std::vector<Expr> vars =
          d_eparser.parseAndBindSortedVarList(impls);
      if (!impls.empty())
      {
        // If there were implicit variables, we go back and refine what is
        // bound in the body to only include the explicit arguments. This
        // ensures that `T` is not parsable in the body of a definition like:
        //   (define test ((T Type :implicit) (x T)) T)
        // It should not be parsable since it is not bound when test is applied,
        // which prevents users from generating definitions that lead to
        // unexpected unbound arguments.
        d_state.popScope();
        d_state.pushScope();
        for (const Expr& e : vars)
        {
          d_state.bind(e.getSymbol(), e);
        }
      }
      Expr ret;
      if (tok == Token::DEFINE_FUN)
      {
        ret = d_eparser.parseType();
      }
      else if (tok == Token::DEFINE_TYPE)
      {
        ret = d_state.mkType();
      }
      Expr expr = d_eparser.parseExpr();
      // ensure we have the right type
      if (!ret.isNull())
      {
        d_eparser.typeCheck(expr, ret);
      }
      d_state.popScope();
      if (tok == Token::DEFINE_FUN)
      {
        // This is for reference checking only. Note that = and lambda are
        // not builtin symbols, thus we must assume they are defined by the user.
        // We assume that a symbol named "=" has been defined.
        Expr eq = d_state.getVar("=");
        if (eq.isNull())
        {
          d_lex.parseError("Expected symbol '=' to be defined when parsing define-fun.");
        }
        Expr rhs = expr;
        Expr t = ret;
        if (!vars.empty())
        {
          // We assume that a symbol named "lambda" has been defined as a binder.
          Expr lambda = d_state.getVar("lambda");
          if (lambda.isNull())
          {
            d_lex.parseError("Expected symbol 'lambda' to be defined when parsing define-fun.");
          }
          Expr bvl = d_state.mkBinderList(lambda.getValue(), vars);
          rhs = d_state.mkExpr(Kind::APPLY, {lambda, bvl, rhs});
          std::vector<Expr> types;
          for (Expr& e : vars)
          {
            types.push_back(d_eparser.typeCheck(e));
          }
          t = d_state.mkFunctionType(types, t, false);
        }
        Expr sym = d_state.mkSymbol(Kind::CONST, name, t);
        Trace("define") << "Define: " << name << " -> " << sym << std::endl;
        d_eparser.bind(name, sym);
        Expr a = d_state.mkExpr(Kind::APPLY, {eq, sym, rhs});
        Trace("define") << "Define-fun reference assert " << a << std::endl;
        d_state.addReferenceAssert(a);
      }
      else
      {
        // defines as a macro
        // make a lambda if given arguments
        if (vars.size() > 0)
        {
          Expr vl = d_state.mkExpr(Kind::TUPLE, vars);
          expr = d_state.mkExpr(Kind::LAMBDA, {vl, expr});
        }
        d_eparser.bind(name, expr);
        Trace("define") << "Define: " << name << " -> " << expr << std::endl;
        // define additionally takes attributes
        if (tok == Token::DEFINE)
        {
          AttrMap attrs;
          d_eparser.parseAttributeList(Kind::LAMBDA, expr, attrs);
        }
      }
    }
    break;
    // (define-sort <symbol> (<symbol>*) <sort>)
    case Token::DEFINE_SORT:
    {
      //d_state.checkThatLogicIsSet();
      std::string name = d_eparser.parseSymbol();
      //d_state.checkUserSymbol(name);
      std::vector<Expr> vars;
      std::vector<std::string> snames =
          d_eparser.parseSymbolList();
      if (!snames.empty())
      {
        d_state.pushScope();
        std::vector<Expr> sorts;
        Expr ttype = d_state.mkType();
        for (const std::string& sname : snames)
        {
          Expr v = d_state.mkSymbol(Kind::PARAM, sname, ttype);
          d_eparser.bind(sname, v);
          vars.push_back(v);
        }
      }
      Expr t = d_eparser.parseType();
      if (!snames.empty())
      {
        d_state.popScope();
        Expr vl = d_state.mkExpr(Kind::TUPLE, vars);
        t = d_state.mkExpr(Kind::LAMBDA, {vl, t});
      }
      d_eparser.bind(name, t);
    }
    break;
    // (echo <string>)
    case Token::ECHO:
    {
      // optional string literal
      tok = d_lex.peekToken();
      if (tok == Token::STRING_LITERAL)
      {
        std::string msg = d_eparser.parseStr(true);
        std::cout << msg << std::endl;
      }
      else
      {
        std::cout << std::endl;
      }
    }
    break;
    // (exit)
    case Token::EXIT:
    {
      d_isFinished = true;
    }
    break;
    case Token::INCLUDE:
    case Token::REFERENCE:
    {
      bool isReference = (tok==Token::REFERENCE);
      if (isReference)
      {
        if (d_state.hasReference())
        {
          d_lex.parseError("Cannot use more than one reference");
        }
      }
      if (d_state.getAssumptionLevel()>0)
      {
        d_lex.parseError("Includes must be done at assumption level zero");
      }
      tok = d_lex.peekToken();
      if (tok != Token::STRING_LITERAL)
      {
        d_lex.parseError("Expected string literal for include");
      }
      // include the file
      std::string file = d_eparser.parseStr(true);
      // read the optional reference normalize function
      Expr referenceNf;
      if (isReference && d_lex.peekToken()!=Token::RPAREN)
      {
        referenceNf = d_eparser.parseExpr();
      }
      // if not reference, it is a signature
      if (!d_state.includeFile(file, !isReference, isReference, referenceNf))
      {
        std::stringstream ss;
        ss << "Cannot include file " << file;
        d_lex.parseError(ss.str());
      }
    }
    break;
    // (program <symbol> <keyword>? (<sorted_var>*) (<sort>*) <sort> (<term_pair>+)?)
    case Token::PROGRAM:
    {
      std::string name = d_eparser.parseSymbol();
      if (d_lex.peekToken()==Token::KEYWORD)
      {
        std::string keyword = d_eparser.parseKeyword();
        if (keyword!="ethos")
        {
          d_lex.parseError("Unsupported program format");
        }
      }
      // push the scope
      d_state.pushScope();
      std::vector<Expr> vars = d_eparser.parseAndBindSortedVarList();
      std::vector<Expr> argTypes = d_eparser.parseTypeList();
      Expr retType = d_eparser.parseType();
      Expr progType = retType;
      if (!argTypes.empty())
      {
        progType = d_state.mkFunctionType(argTypes, retType, false);
      }
      // it may have been forward declared
      Expr pprev = d_state.getVar(name);
      Expr pvar;
      if (!pprev.isNull())
      {
        if (pprev.getKind()!=Kind::PROGRAM_CONST)
        {
          std::stringstream ss;
          ss << "Already declared symbol " << name << " as a non-program";
          d_lex.parseError(ss.str());
        }
        // should not already have a definition
        Expr prevProg = d_state.getProgram(pprev.getValue());
        if (!prevProg.isNull())
        {
          d_lex.parseError("Cannot define program more than once");
        }
        // it should be a program with the same type
        d_eparser.typeCheck(pprev, progType);
        pvar = pprev;
      }
      else
      {
        // the type of the program variable is a function
        pvar = d_state.mkSymbol(Kind::PROGRAM_CONST, name, progType);
        // bind the program, temporarily
        d_eparser.bind(name, pvar);
      }
      Expr program;
      tok = d_lex.peekToken();
      // if RPAREN follows, it is a forward declaration, we do not define the program
      if (tok!=Token::RPAREN)
      {
        // parse the body
        std::vector<Expr> pchildren = d_eparser.parseExprPairList();
        if (pchildren.empty())
        {
          d_lex.parseError("Expected non-empty list of cases");
        }
        // ensure program cases are
        // (A) applications of the program
        // (B) have arguments that are not evaluatable
        for (Expr& p : pchildren)
        {
          Expr pc = p[0];
          if (pc.getKind() != Kind::APPLY || pc[0] != pvar)
          {
            d_lex.parseError("Expected application of program as case");
          }
          if (pc.getNumChildren() != argTypes.size() + 1)
          {
            d_lex.parseError("Wrong arity for pattern");
          }
          // ensure some type checking??
          //d_eparser.typeCheck(pc);
          // ensure the right hand side is bound by the left hand side
          std::vector<Expr> bvs = Expr::getVariables(pc);
          Expr rhs = p[1];
          d_eparser.ensureBound(rhs, bvs);
          // TODO: allow variable or default case?
          for (size_t i = 0, nchildren = pc.getNumChildren(); i < nchildren; i++)
          {
            Expr ecc = pc[i];
            if (ecc.isEvaluatable())
            {
              std::stringstream ss;
              ss << "Cannot match on evaluatable subterm " << pc[i];
              d_lex.parseError(ss.str());
            }
          }
        }
        program = d_state.mkExpr(Kind::PROGRAM, pchildren);
      }
      d_state.popScope();
      if (!program.isNull())
      {
        d_state.defineProgram(pvar, program);
      }
      if (pprev.isNull())
      {
        // rebind the program, if new
        d_eparser.bind(name, pvar);
      }
    }
    break;
    // (reset)
    case Token::RESET:
    {
      // reset the state of the parser, which is independent of the symbol
      // manager
      d_state.reset();
    }
    break;
    // (step i F? :rule R :premises (p1 ... pn) :args (t1 ... tm))
    // which is syntax sugar for
    // (define-const i (Proof F) (R t1 ... tm p1 ... pn))
    // The parameters :premises and :args can be omitted if empty 
    case Token::STEP:
    case Token::STEP_POP:
    {
      bool isPop = (tok==Token::STEP_POP);
      std::string name = d_eparser.parseSymbol();
      Trace("step") << "Check step " << name << std::endl;
      Expr proven;
      // see if we have proven
      tok = d_lex.peekToken();
      if (tok != Token::KEYWORD)
      {
        proven = d_eparser.parseFormula();
      }
      // parse rule name
      std::string keyword = d_eparser.parseKeyword();
      if (keyword!="rule")
      {
        d_lex.parseError("Expected rule in step");
      }
      std::string ruleName = d_eparser.parseSymbol();
      Expr rule = d_eparser.getProofRule(ruleName);
      RuleStat * rs = &d_sts.d_rstats[rule.getValue()];
      if (d_statsEnabled)
      {
        RuleStat::start(d_sts);
      }
      // parse premises, optionally
      if (d_lex.peekToken()==Token::KEYWORD)
      {
        keyword = d_eparser.parseKeyword();
      }
      std::vector<Expr> premises;
      if (keyword=="premises")
      {
        std::vector<Expr> given = d_eparser.parseExprList();
        // maybe combine premises
        if (!d_state.getActualPremises(rule.getValue(), given, premises))
        {
          d_lex.parseError("Failed to get premises");
        }
        if (d_lex.peekToken()==Token::KEYWORD)
        {
          keyword = d_eparser.parseKeyword();
        }
      }
      // parse args, optionally
      std::vector<Expr> args;
      if (keyword=="args")
      {
        args = d_eparser.parseExprList();
      }
      std::vector<Expr> children;
      children.push_back(rule);
      children.insert(children.end(), args.begin(), args.end());
      // premises after arguments
      children.insert(children.end(), premises.begin(), premises.end());
      // the assumption, if pop
      if (isPop)
      {
        if (d_state.getAssumptionLevel()==0)
        {
          d_lex.parseError("Cannot pop at level zero");
        }
        std::vector<Expr> as = d_state.getCurrentAssumptions();
        Assert (as.size()==1);
        // push the assumption
        children.push_back(as[0]);
      }
      // compute the type of applying the rule
      Expr concType;
      if (children.size()>1)
      {
        // check type rule for APPLY directly without constructing the app
        concType = d_eparser.typeCheckApp(children);
      }
      else
      {
        concType = d_eparser.typeCheck(rule);
      }
      // if we specified a conclusion, we will possibly evaluate the type
      // under the substitution `eo::conclusion -> proven`. We only do this
      // if we did not already match what was proven.
      if (!proven.isNull())
      {
        if (concType.getKind()!=Kind::PROOF_TYPE || concType[0]!=proven)
        {
          Ctx cctx;
          cctx[d_state.mkConclusion().getValue()] = proven.getValue();
          concType = d_state.getTypeChecker().evaluate(concType.getValue(), cctx);
        }
      }
      // ensure proof type, note this is where "proof checking" happens.
      if (concType.getKind() != Kind::PROOF_TYPE)
      {
        std::stringstream ss;
        ss << "Non-proof conclusion for rule " << ruleName << ", got " << concType;
        d_lex.parseError(ss.str());
      }
      // Check that the proved term is actually Bool
      Expr concTerm = concType[0];
      Expr concTermType = d_eparser.typeCheck(concTerm);
      if (concTermType.getKind() != Kind::BOOL_TYPE)
      {
        std::stringstream ss;
        ss << "Non-bool conclusion for step, got " << concTermType;
        d_lex.parseError(ss.str());
      }
      if (!proven.isNull())
      {
        if (concType[0]!=proven)
        {
          std::stringstream ss;
          ss << "Unexpected conclusion for rule " << ruleName << ":" << std::endl;
          ss << "    Proves: " << concType << std::endl;
          ss << "  Expected: (Proof " << proven << ")";
          d_lex.parseError(ss.str());
        }
      }
      // pop the assumption scope, before it is bound
      if (isPop)
      {
        d_state.popAssumptionScope();
      }
      // bind to variable, note that the definition term is not kept
      Expr v = d_state.mkSymbol(Kind::CONST, name, concType);
      d_eparser.bind(name, v);
      // d_eparser.bind(name, def);
      Assert (rs!=nullptr);
      // increment the count regardless of whether stats are enabled, since it
      // may impact whether we report incomplete
      rs->d_count++;
      if (d_statsEnabled)
      {
        // increment the stats
        rs->increment(d_sts);
      }
    }
    break;
    //-------------------------- commands to support reading ordinary smt2 inputs
    // (assert <formula>)
    case Token::ASSERT:
    {
      Expr a = d_eparser.parseFormula();
      d_state.addReferenceAssert(a);
    }
    break;
    // (check-sat)
    case Token::CHECK_SAT:
    break;
    // (check-sat-assuming (<formula>*))
    case Token::CHECK_SAT_ASSUMING:
    {
      d_eparser.parseExprList();
    }
    break;
    case Token::POP:
    case Token::PUSH:
    {
      bool isPush = (tok==Token::PUSH);
      tok = d_lex.peekToken();
      size_t num = 1;
      if (tok == Token::INTEGER_LITERAL)
      {
        num = d_eparser.parseIntegerNumeral();
      }
      for (size_t i=0; i<num; i++)
      {
        if (isPush)
        {
          d_state.pushScope();
        }
        else
        {
          d_state.popScope();
        }
      }
    }
    break;
    // (set-logic <logic>)
    case Token::SET_LOGIC:
    {
      d_eparser.parseSymbol();
    }
    break;
    // (set-info <attribute> <sexpr>)
    case Token::SET_INFO:
    {
      std::string key = d_eparser.parseKeyword();
      d_eparser.parseSymbolicExpr();
    }
    break;
    // (set-option <option> <sexpr>)
    case Token::SET_OPTION:
    {
      std::string key = d_eparser.parseKeyword();
      // if reference, we always ignore this command
      if (!d_isReference)
      {
        // otherwise, it may be an Ethos option
        bool success = false;
        if (d_lex.peekToken() == Token::SYMBOL)
        {
          std::string str(d_lex.tokenStr());
          if (str == "true" || str == "false")
          {
            success = d_state.getOptions().setOption(key, str == "true");
          }
        }
        if (!success)
        {
          Warning() << "Unsupported option or value for option " << key
                    << std::endl;
        }
      }
      // now parse the symbol
      d_eparser.parseSymbolicExpr();
    }
    break;
    case Token::EOF_TOK:
      d_lex.parseError("Expected Eunoia command", true);
      break;
    default:
      d_lex.unexpectedTokenError(tok, "Expected Eunoia command");
      break;
  }
  d_lex.eatToken(Token::RPAREN);
  return true;
}

}  // namespace ethos
