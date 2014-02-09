#pragma once

#include "pintool.h"
#include "TaintObject.h"    // références croisées de classe 
// cf http://cpp.developpez.com/faq/cpp/index.php?page=classes#CLASS_reference_croisee

// classe représentant les sources d'un objet
class ObjectSource 
{ 
private:    
    UINT32    m_len;
    TaintPtr  m_src;
    ADDRINT   m_val;   // 32 ou 64bits selon la compilation 
public:
    ObjectSource() {};
    ObjectSource(const TaintPtr &taintPtr);
    ObjectSource(UINT32 length, ADDRINT value);
    ~ObjectSource() {} 

    UINT32  getLength() const;
    bool    isSrcTainted() const;
    ADDRINT getValue() const;
    const   TaintPtr& getTaintedSource() const;
};