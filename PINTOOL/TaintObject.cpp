#pragma once

#include "TaintObject.h"
#include "ObjectSource.h"

// TAINT : classe représentant un objet marqué
Taint::Taint(Relation rel, UINT32 lengthInBits) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{}

Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
}

Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
}

Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
                                       const ObjectSource &os3) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
}

Taint::Taint(Relation rel, UINT32 lengthInBits, const ObjectSource &os1, const ObjectSource &os2, 
                                       const ObjectSource &os3, const ObjectSource &os4) 
    : _lengthInBits(lengthInBits), _sourceRelation(rel), _isDeclaredFlag(false) 
{
    this->_sources.push_back(os1);
    this->_sources.push_back(os2);
    this->_sources.push_back(os3);
    this->_sources.push_back(os4);
}

Taint::~Taint() { }

// renvoie la longueur en bits de l'objet
const UINT32 Taint::getLength() const { return (this->_lengthInBits); }

// renvoie le type de relation qui lie cet objet à ses sources
const Relation Taint::getSourceRelation() const { return (this->_sourceRelation); } 

// retourne VRAI si l'objet a été déclaré dans la formule à destination du solveur
bool Taint::isDeclared() const  { return (this->_isDeclaredFlag); }

// indique que l'objet a été déclaré dans la formule à destination du solveur
void Taint::setDeclared() { this->_isDeclaredFlag = true; }

void Taint::setName(const std::string &name) { this->_objectName = name; }

const std::string& Taint::getName() const { return (this->_objectName); }

std::vector<ObjectSource>& Taint::getSources() { return (this->_sources); }

ObjectSource& Taint::getSources(UINT32 i) { return (this->_sources.at(i)); }

void Taint::addSource(const TaintPtr &taintPtr) { this->_sources.push_back(ObjectSource(taintPtr)); }

void Taint::addSource(const ObjectSource &src) { this->_sources.push_back(src); }   

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

template<UINT32 lengthInBits> TaintObject<lengthInBits>::~TaintObject() {}

// instanciation des templates utilisés (ici car références croisées)
class Taint;
template class TaintObject<1>;
template class TaintObject<8>;
template class TaintObject<16>;
template class TaintObject<32>;
template class TaintObject<64>;
template class TaintObject<128>;