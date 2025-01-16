/******************************************************************************
 * This file is part of the ethos project.
 *
 * Copyright (c) 2023-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 ******************************************************************************/
#include "attr.h"

namespace ethos {

std::ostream& operator<<(std::ostream& o, Attr a)
{
  switch (a)
  {
    case Attr::NONE: o << "NONE"; break;
    case Attr::VAR: o << "VAR"; break;
    case Attr::IMPLICIT: o << "IMPLICIT"; break;
    case Attr::TYPE: o << "TYPE"; break;
    case Attr::SORRY: o << "SORRY"; break;
    case Attr::LIST: o << "LIST"; break;
    case Attr::REQUIRES: o << "REQUIRES"; break;
    case Attr::PREMISE_LIST: o << "PREMISE_LIST"; break;
    case Attr::PROGRAM: o << "PROGRAM"; break;
    case Attr::ORACLE: o << "ORACLE"; break;
    case Attr::BINDER: o << "BINDER"; break;
    case Attr::LET_BINDER: o << "LET_BINDER"; break;
    case Attr::OPAQUE: o << "OPAQUE"; break;
    case Attr::SYNTAX: o << "SYNTAX"; break;
    case Attr::RESTRICT: o << "RESTRICT"; break;
    case Attr::RIGHT_ASSOC: o << "RIGHT_ASSOC"; break;
    case Attr::LEFT_ASSOC: o << "LEFT_ASSOC"; break;
    case Attr::RIGHT_ASSOC_NIL: o << "RIGHT_ASSOC_NIL"; break;
    case Attr::LEFT_ASSOC_NIL: o << "LEFT_ASSOC_NIL"; break;
    case Attr::CHAINABLE: o << "CHAINABLE"; break;
    case Attr::PAIRWISE: o << "PAIRWISE"; break;
    case Attr::DATATYPE: o << "DATATYPE"; break;
    case Attr::CODATATYPE: o << "CODATATYPE"; break;
    case Attr::DATATYPE_CONSTRUCTOR: o << "DATATYPE_CONSTRUCTOR"; break;
    case Attr::AMB_DATAYPE_CONSTRUCTOR: o << "AMB_DATAYPE_CONSTRUCTOR"; break;
    default: o << "UnknownAttr(" << unsigned(a) << ")"; break;
  }
  return o;
}

bool isNAryAttr(Attr a)
{
  switch (a)
  {
    case Attr::LEFT_ASSOC:
    case Attr::RIGHT_ASSOC:
    case Attr::LEFT_ASSOC_NIL:
    case Attr::RIGHT_ASSOC_NIL:
    case Attr::CHAINABLE:
    case Attr::PAIRWISE:
      return true;
    default:
      break;
  }
  return false;
}

bool isConstructorKindAttr(Attr a)
{
  return isNAryAttr(a) || a==Attr::BINDER || a==Attr::LET_BINDER || a==Attr::LIST;
}

}  // namespace ethos
