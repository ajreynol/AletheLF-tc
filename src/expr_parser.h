/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef EXPR_PARSER_H
#define EXPR_PARSER_H

#include "expr.h"
#include "state.h"
#include "lexer.h"
#include "attr.h"

namespace alfc {

/**
 * The smt2 term parser, which parses terms, sorts, symbol expressions
 * and other miscellaneous expressions from the SMT2 language. It reads
 * from the given lexer.
 */
class ExprParser
{
 public:
  ExprParser(Lexer& lex, State& state, bool isReference);
  virtual ~ExprParser() {}

  /** Parses an SMT-LIB term <term> */
  Expr parseExpr();
  /** Parses an SMT-LIB type <type> */
  Expr parseType();
  /** Parses an SMT-LIB formula <formula> */
  Expr parseFormula();
  /** Parses an SMT-LIB term pair */
  Expr parseExprPair();
  /** Parses a symbolic expression */
  std::string parseSymbolicExpr();
  /** Parses parentheses-enclosed term list (<term>*) */
  std::vector<Expr> parseExprList();
  /** Parses parentheses-enclosed term list (<type>*) */
  std::vector<Expr> parseTypeList();
  /** Parses parentheses-enclosed term list ((<term> <term>)*) */
  std::vector<Expr> parseExprPairList();
  /**
   * Parse parentheses-enclosed sorted variable list of the form:
   * ((<symbol> <sort>)*)
   * 
   * @param isLookup If true, we expect the variable list to be already bound
   * variables and throw an error if a variable does not match.
   */
  std::vector<Expr> parseAndBindSortedVarList(bool isLookup=false);
  /**
   * Same as above, but tracks implicit variables. All variables marked
   * :implicit that were parsed and not added to the return value of this
   * method are added to impls.
   */
  std::vector<Expr> parseAndBindSortedVarList(std::vector<Expr>& impls,
                                              bool isLookup=false);
  /**
   * Parse symbol, which returns the string of the parsed symbol if the next
   * token is a valid smt2 symbol.
   *
   * @param check Specifies whether to check if the symbol is already declared
   * or not declared,
   * @param type The type of symbol we are expecting (variable or sort).
   */
  std::string parseSymbol();
  /**
   * Parse parentheses-enclosed symbol list.
   * Expects to parse '(<symbol>*)', where '<symbol>' is parsed by the above
   * method.
   */
  std::vector<std::string> parseSymbolList();
  /**
   * Parse datatype def '<datatype_dec>', not parentheses enclosed. The syntax
   * for datatype declarations is:
   *
   * datatype_dec :=
   *   (<constructor_dec>+) | (par (<symbol>+) (<constructor_dec>+))
   * constructor_dec := (<symbol> (<symbol> <sort>)∗)
   */
  bool parseDatatypesDef(const std::vector<std::string>& dnames,
                         const std::vector<size_t>& arities,
                         std::map<const ExprValue*, std::vector<Expr>>& dts,
                         std::map<const ExprValue*, std::vector<Expr>>& dtcons);
  /**
   * Parses ':X', returns 'X'
   */
  std::string parseKeyword();
  /** Parse integer numeral */
  uint32_t parseIntegerNumeral();
  /**
   * Matches a string, and (optionally) strips off the quotes/unescapes the
   * string when `unescape` is set to true.
   */
  std::string parseStr(bool unescape);
  
  /**
   * Parse attribute list
   * <attr_1> ... <attr_n>
   * 
   * @param e The expression we are applying to
   * @param attr The attributes which are populated
   * @param pushedScope True if we pushed a scope while reading the list. This
   * is true when e.g. the attribute :var is read. The caller of this method
   * is responsible for popping the scope.
   */
  void parseAttributeList(Expr& e, AttrMap& attrs, bool& pushedScope);
  /** Same as above, but ensures we pop the scope */
  void parseAttributeList(Expr& e, AttrMap& attrs);
  /**
   * Parse a format, which is a keyword. If none is provided, ALF is returned.
   */
  Format parseFormat();
  /**
   * Parse literal kind.
   */
  Kind parseLiteralKind();
  
  //-------------------------- checking
  /** type check the expression */
  Expr typeCheck(Expr& e);
  /** type check (APPLY children), without constructing the APPLY */
  Expr typeCheckApp(std::vector<Expr>& children);
  /** ensure type */
  Expr typeCheck(Expr& e, const Expr& expected);
  /** get variable, else error */
  Expr getVar(const std::string& name);
  /** get variable, else error */
  Expr getProofRule(const std::string& name);
  /** Bind, or throw error otherwise */
  void bind(const std::string& name, Expr& e);
  /** Ensure bound */
  void ensureBound(const Expr& e, const std::vector<Expr>& bvs);
  //-------------------------- end checking
  /** Get constructor kind */
  void processAttributeMap(const AttrMap& attrs, Attr& ck, Expr& cons, const std::vector<Expr>& params);
 protected:
  /**
   * Parse constructor definition list, add to declaration type. The expected
   * syntax is '(<constructor_dec>+)'.
   */
  void parseConstructorDefinitionList(
      Expr& dt,
      std::vector<Expr>& conslist,
      std::map<const ExprValue*, std::vector<Expr>>& dtcons,
      std::vector<std::pair<std::string, Expr>>& toBind);
  /** Return the unsigned for the current token string. */
  uint32_t tokenStrToUnsigned();
  /**
   * Return the string content of the current token string when interpreted
   * as the given token, e.g. return`abc` for token string `|abc|` where
   * tok is QUOTED_SYMBOL.
   */
  std::string tokenStrToSymbol(Token tok);
  /**
   * Unescape string, which updates s based on processing escape sequences
   * as defined in SMT2.
   */
  void unescapeString(std::string& s);
  /** The null expression */
  Expr d_null;
  /** The lexer */
  Lexer& d_lex;
  /** The state */
  State& d_state;
  /** */
  bool d_isReference;
  /** Strings to attributes */
  std::map<std::string, Attr> d_strToAttr;
  /** Mapping strings to literal kinds */
  std::map<std::string, Kind> d_strToLiteralKind;
  /** Mapping strings to formats */
  std::map<std::string, Format> d_strToFormat;
};

}  // namespace cvc5

#endif /* TERM_PARSER_H */
