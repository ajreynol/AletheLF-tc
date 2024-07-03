/******************************************************************************
 * This file is part of the alfc project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#ifndef TOKENS_H
#define TOKENS_H

#include <sstream>
#include <string>

namespace alfc {

/**
 * Tokens for parsing.
 */
enum class Token
{
  EOF_TOK = 0,
  ABSTRACT_TYPE,
  ASSERT,
  ASSUME,
  ASSUME_PUSH,
  ATTRIBUTE,
  BOOL_TYPE,
  BINARY_LITERAL,
  CHECK_SAT,
  CHECK_SAT_ASSUMING,
  DECIMAL_LITERAL,
  DECLARE_CODATATYPE,
  DECLARE_CODATATYPES,
  DECLARE_CONST,
  DECLARE_CONSTS,
  DECLARE_DATATYPE,
  DECLARE_DATATYPES,
  DECLARE_FUN,
  DECLARE_PARAMETERIZED_CONST,
  DECLARE_ORACLE_FUN,
  DECLARE_RULE,
  DECLARE_SORT,
  DECLARE_TYPE,
  DECLARE_VAR,
  DEFINE,
  DEFINE_CONST,
  DEFINE_FUN,
  DEFINE_SORT,
  DEFINE_TYPE,
  ECHO,
  EVAL_DEFINE,  // alf.define
  EVAL_MATCH,   // alf.match
  EXIT,
  HEX_LITERAL,
  INCLUDE,
  INTEGER_LITERAL,
  KEYWORD,
  LET,
  LPAREN,
  NUMERAL,
  PAR,
  POP,
  PROGRAM,
  PROOF,
  PROOF_TYPE,
  PUSH,
  QUOTED_SYMBOL,
  RATIONAL_LITERAL,
  REFERENCE,
  RESET,
  RPAREN,
  SET_INFO,
  SET_LOGIC,
  SET_OPTION,
  STEP,
  STEP_POP,
  STRING_LITERAL,
  SYMBOL,
  TYPE,
  UNTERMINATED_QUOTED_SYMBOL,
  UNTERMINATED_STRING_LITERAL,
  NONE
};

/** Print a token to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Token t);

/**
 * Rule format.
 */
enum class Format
{
  ALF,
  RARE,
  NONE
};

/** Print a format to the stream, for debugging */
std::ostream& operator<<(std::ostream& o, Format f);

}  // namespace alfc

#endif /* TOKENS_H */
