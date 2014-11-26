#pragma once

#include <pintool.h>
#include "TaintObject.h"    // références croisées de classe 
// cf http://cpp.developpez.com/faq/cpp/index.php?page=classes#CLASS_reference_croisee

// classe représentant les sources d'un objet
class ObjectSource 
{ 
private:    
    TaintPtr  _src;
    ADDRINT   _val;   // 32 ou 64bits selon la compilation
    UINT32    _lengthInBits; 
public:
    ObjectSource();
    ObjectSource(const TaintPtr &taintPtr);
    ObjectSource(UINT32 lengthInBits, ADDRINT value);

    /** RULE OF FIVE **/
    // copy constructor
    ObjectSource(const ObjectSource& other);
    // move constructor
    ObjectSource(ObjectSource&& other);
    // copy assignment operator
    ObjectSource& operator= (ObjectSource& other);
    // move assignment operator
    ObjectSource& operator= (ObjectSource&& other);
    // destructor (vide)
    ~ObjectSource() {}

    UINT32  getLength() const;
    bool    isSrcTainted() const;
    ADDRINT getValue() const;
    TaintPtr getTaintedSource() const;
};