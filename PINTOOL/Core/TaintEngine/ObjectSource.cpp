#include "ObjectSource.h"

// OBJECTSOURCE : classe représentant les sources d'un objet

ObjectSource::ObjectSource() : _src(nullptr), _val(0), _lengthInBits(0) {}

// constructeur pour source de type marquée
ObjectSource::ObjectSource(const TaintPtr &taintPtr)     
    : _src(taintPtr),  
      _val(0),  
      _lengthInBits(taintPtr->getLength()) {}   

// constructeur pour source de type valeur
ObjectSource::ObjectSource(UINT32 lengthInBits, ADDRINT value)
    : _src(nullptr),   
      _val(value), 
      _lengthInBits(lengthInBits) {} 

UINT32 ObjectSource::getLength() const  { return (_lengthInBits); }

bool ObjectSource::isSrcTainted() const { return ((bool) _src); }

ADDRINT ObjectSource::getValue() const  { return (_val); }

TaintPtr ObjectSource::getTaintedSource() const  { return (_src); }