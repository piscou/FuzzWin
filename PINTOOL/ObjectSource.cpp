#include "ObjectSource.h"

// OBJECTSOURCE : classe représentant les sources d'un objet

// constructeur pour source de type marquée
ObjectSource::ObjectSource(const TaintPtr &taintPtr)     
    : m_src(taintPtr),  
      m_val(0),  
      m_len(taintPtr->getLength()) {}   

// constructeur pour source de type valeur
ObjectSource::ObjectSource(UINT32 length, ADDRINT value)
    : m_src(nullptr),   
      m_val(value), 
      m_len(length) {} 

UINT32 ObjectSource::getLength() const
{ return (this->m_len); }

bool ObjectSource::isSrcTainted() const
{ return ((bool) this->m_src); }

ADDRINT ObjectSource::getValue() const
{ return (this->m_val); }

const TaintPtr& ObjectSource::getTaintedSource() const
{ return (this->m_src); }

#if DEBUG
UINT32 ObjectSource::getId() const 
{ return ( (bool)this->m_src ? this->m_src->getId() : 0); }
#endif