#pragma once

#include "TaintObject.h"
#include "ObjectSource.h"

/** TAINT : classe représentant un objet marqué **/

// constructeur sans sources
Taint::Taint(Relation rel, UINT32 lengthInBits) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{}

// constructeur avec 1 source
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    _sources.push_back(os1);
}

// constructeur avec 2 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
}

// constructeur avec 3 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
                                       const ObjectSource &os3) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
}

// constructeur avec 4 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
                                       const ObjectSource &os3, const ObjectSource &os4) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
    this->_sources.push_back(os4);
}

const UINT32 Taint::getLength() const { return (_lengthInBits); }

// renvoie le type de relation qui lie cet objet à ses sources
const Relation Taint::getSourceRelation() const { return (_sourceRelation); } 

// retourne VRAI si l'objet a été déclaré dans la formule à destination du solveur
bool Taint::isDeclared() const  { return (_isDeclaredFlag); }

void Taint::setDeclared() { _isDeclaredFlag = true; }

void Taint::setName(const std::string &name) { _objectName = name; }

const std::string& Taint::getName() const { return (_objectName); }

const std::vector<ObjectSource>& Taint::getSources() const { return (_sources); }

const ObjectSource& Taint::getSource(UINT32 i) const { return (_sources.at(i)); }

void Taint::addSource(const TaintPtr &taintPtr) { _sources.push_back(ObjectSource(taintPtr)); }

void Taint::addSource(const ObjectSource &src) { _sources.push_back(src); }   

// définit les détails supplémentaires pour cet objet (mode verbose)
void Taint::setVerboseDetails(const std::string &data) { _additionalData = data; }

// retourne les détails supplémentaires de cet objet (mode verbose)
const std::string& Taint::getVerboseDetails() const { return _additionalData; }

/** TAINTOBJECT : classe dérivée **/

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel) : Taint(rel, lengthInBits) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1) 
    : Taint(rel, lengthInBits, os1) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2) 
    : Taint(rel, lengthInBits, os1, os2) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2, 
                                               const ObjectSource &os3) 
    : Taint(rel, lengthInBits, os1, os2, os3) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2, 
                                               const ObjectSource &os3, const ObjectSource &os4) 
    : Taint(rel, lengthInBits, os1, os2, os3, os4) {}

// instanciation des templates utilisés (ici car références croisées)
class Taint;
template class TaintObject<1>;
template class TaintObject<8>;
template class TaintObject<16>;
template class TaintObject<32>;
template class TaintObject<64>;
template class TaintObject<128>;