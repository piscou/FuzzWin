#pragma once

#include "TaintObject.h"
#include "ObjectSource.h"

// TAINT : classe représentant un objet marqué
Taint::Taint(Relation rel, UINT32 len) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1, const ObjectSource &os2) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
    this->m_sources.push_back(os2);
}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1, const ObjectSource &os2, const ObjectSource &os3) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
    this->m_sources.push_back(os2);
    this->m_sources.push_back(os3);
}

Taint::~Taint() { }

// renvoie la longueur en bits de l'objet
const UINT32 Taint::getLength() const { return (this->m_len); }

// renvoie le type de relation qui lie cet objet à ses sources
const Relation Taint::getSourceRelation() const { return (this->m_sourceRelation); } 

// retourne VRAI si l'objet a été déclaré dans la formule à destination du solveur
bool Taint::isDeclared() const  { return (this->m_isDeclaredFlag); }

// indique que l'objet a été déclaré dans la formule à destination du solveur
void Taint::setDeclared() { this->m_isDeclaredFlag = true; }

void Taint::setName(const std::string &name) { this->m_objectName = name; }

const std::string& Taint::getName() const { return (this->m_objectName); }

std::vector<ObjectSource>& Taint::getSources() { return (this->m_sources); }

ObjectSource& Taint::getSources(UINT32 i) { return (this->m_sources.at(i)); }

void Taint::addSource(const TaintPtr &taintPtr) { this->m_sources.push_back(ObjectSource(taintPtr)); }

void Taint::addSource(const ObjectSource &src) { this->m_sources.push_back(src); }   

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel) : Taint(rel, length) {}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1) 
    : Taint(rel, length, os1) {}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2) 
    : Taint(rel, length, os1, os2) {}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2, const ObjectSource &os3) 
    : Taint(rel, length, os1, os2, os3) {}

template<UINT32 len> TaintObject<len>::~TaintObject() {}

// instanciation des templates utilisés (ici car références croisées)
class Taint;
template class TaintObject<1>;
template class TaintObject<8>;
template class TaintObject<16>;
template class TaintObject<32>;
template class TaintObject<64>;
template class TaintObject<128>;