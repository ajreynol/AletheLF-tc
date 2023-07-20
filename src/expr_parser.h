#ifndef EXPR_PARSER_H
#define EXPR_PARSER_H

#include "expr.h"
#include "state.h"
#include "lexer.h"
#include "attr.h"

namespace atc {

/**
 * The smt2 term parser, which parses terms, sorts, symbol expressions
 * and other miscellaneous expressions from the SMT2 language. It reads
 * from the given lexer.
 */
class ExprParser
{
 public:
  ExprParser(Lexer& lex, State& state);
  virtual ~ExprParser() {}

  /** Parses an SMT-LIB term <term> */
  Expr parseExpr();
  /** Parses parentheses-enclosed term list (<term>*) */
  std::vector<Expr> parseExprList();
  /**
   * Parse parentheses-enclosed sorted variable list of the form:
   * ((<symbol> <sort>)*)
   */
  std::vector<Expr> parseAndBindSortedVarList(bool allowList = false);
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
   */
  void parseAttributeList(const Expr& e, std::map<Attr, Expr>& attrs);

  /** type check the expression */
  Expr typeCheck(Expr& e);
  /** ensure type */
  Expr typeCheck(Expr& e, const Expr& expected);
 protected:
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
  /**
   * Parse constructor definition list, add to declaration type. The expected
   * syntax is '(<constructor_dec>+)'.
   */
  //void parseConstructorDefinitionList(DatatypeDecl& type);
  /**
   * Parse match case pattern
   */
  //Expr parseMatchCasePattern(Expr headExpr, std::vector<Expr>& boundVars);
  /** get variable, else error */
  Expr getVar(const std::string& name);
  /** The lexer */
  Lexer& d_lex;
  /** The state */
  State& d_state;
  /** Strings to attributes */
  std::map<std::string, Attr> d_strToAttr;
};

}  // namespace cvc5

#endif /* TERM_PARSER_H */
