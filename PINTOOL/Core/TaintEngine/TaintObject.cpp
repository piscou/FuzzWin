#pragma once

#include "TaintObject.h"
#include "ObjectSource.h"

/** TAINT : classe représentant un objet marqué **/

// constructeur sans sources
Taint::Taint(Relation rel, UINT32 lengthInBits, std::string VerboseDetails) :
    _lengthInBits(lengthInBits), 
    _sourceRelation(rel), 
    _isDeclaredFlag(false),
    _verboseData(std::move(VerboseDetails))
{}

// constructeur avec 1 source
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1,
    std::string VerboseDetails) : 
    _lengthInBits(lengthInBits), 
    _sourceRelation(rel), 
    _isDeclaredFlag(false),
    _verboseData(std::move(VerboseDetails))
{
    _sources.push_back(os1);
}

// constructeur avec 2 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2,
    std::string VerboseDetails) :
    _lengthInBits(lengthInBits), 
    _sourceRelation(rel), 
    _isDeclaredFlag(false),
    _verboseData(std::move(VerboseDetails))
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
}

// constructeur avec 3 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
    const ObjectSource &os3, std::string VerboseDetails) :
    _lengthInBits(lengthInBits), 
    _sourceRelation(rel), 
    _isDeclaredFlag(false),
    _verboseData(std::move(VerboseDetails))
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
}

// constructeur avec 4 sources
Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
    const ObjectSource &os3, const ObjectSource &os4, std::string VerboseDetails) :
    _lengthInBits(lengthInBits), 
    _sourceRelation(rel), 
    _isDeclaredFlag(false),
    _verboseData(std::move(VerboseDetails))
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
    this->_sources.push_back(os4);
}

UINT32 Taint::getLength() const { return (_lengthInBits); }

// renvoie le type de relation qui lie cet objet à ses sources
Relation Taint::getSourceRelation() const { return (_sourceRelation); } 

// renvoie le nombre de sources de l'objet
UINT32 Taint::getNumberOfSources() const { return (_sources.size()); }

// retourne VRAI si l'objet a été déclaré dans la formule à destination du solveur
bool Taint::isDeclared() const  { return (_isDeclaredFlag); }

void Taint::setDeclared() { _isDeclaredFlag = true; }

void Taint::setName(std::string name) { _objectName = std::move(name); } // Passage par RVALUE

std::string Taint::getName() const { return (_objectName); }

std::vector<ObjectSource> Taint::getSources() const { return (_sources); }

ObjectSource Taint::getSource(UINT32 i) const { return (_sources.at(i)); }

void Taint::addSource(const TaintPtr &taintPtr) { _sources.push_back(ObjectSource(taintPtr)); }

void Taint::addSource(ObjectSource src) { _sources.push_back(std::move(src)); }  // Passage par RVALUE

// retourne les détails supplémentaires de cet objet (mode verbose)
std::string Taint::getVerboseDetails() const { return _verboseData; }

/** TAINTOBJECT : classe dérivée **/

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, std::string VerboseDetails) : 
    Taint(rel, lengthInBits, VerboseDetails) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, 
    std::string VerboseDetails) : 
    Taint(rel, lengthInBits, os1, VerboseDetails) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, 
    const ObjectSource &os2, std::string VerboseDetails) :
    Taint(rel, lengthInBits, os1, os2, VerboseDetails) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, 
    const ObjectSource &os2, const ObjectSource &os3, std::string VerboseDetails) :
    Taint(rel, lengthInBits, os1, os2, os3, VerboseDetails) {}

template<UINT32 lengthInBits> 
TaintObject<lengthInBits>::TaintObject(Relation rel, const ObjectSource &os1, 
    const ObjectSource &os2, const ObjectSource &os3, const ObjectSource &os4,
    std::string VerboseDetails) : 
    Taint(rel, lengthInBits, os1, os2, os3, os4, VerboseDetails) {}

// instanciation des templates utilisés (ici car références croisées)
class Taint;
template class TaintObject<1>;
template class TaintObject<8>;
template class TaintObject<16>;
template class TaintObject<32>;
template class TaintObject<64>;
template class TaintObject<128>;