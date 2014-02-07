#pragma once

#include "TaintObject.h"
#include "ObjectSource.h"

// TAINT : classe représentant un objet marqué
Taint::Taint(Relation rel, UINT32 len) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
#if DEBUG
    this->m_id = idValue++;
#endif
}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
    #if DEBUG
    this->m_id = idValue++;
    #endif
}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1, const ObjectSource &os2) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
    this->m_sources.push_back(os2);
    #if DEBUG
    this->m_id = idValue++;
    #endif
}

Taint::Taint(Relation rel, UINT32 len, const ObjectSource &os1, const ObjectSource &os2, const ObjectSource &os3) 
    : m_sourceRelation(rel), m_isDeclaredFlag(false), m_len(len)
{
    this->m_sources.push_back(os1);
    this->m_sources.push_back(os2);
    this->m_sources.push_back(os3);
    #if DEBUG
    this->m_id = idValue++;
    #endif
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
TaintObject<length>::TaintObject(Relation rel) : Taint(rel, length)
{ 
#if 0
    PIN_GetLock(&lock, 0);
    taint << "Nouvel objet TAINT" << std::dec << m_len << " id " << this->m_id;
    taint << " relation : " << enum_strings[rel] << std::endl;
    PIN_ReleaseLock(&lock);
#endif
}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1) 
    : Taint(rel, length, os1)
{ 
    #if 0
    PIN_GetLock(&lock, 0);
    taint << "Nouvel objet TAINT" << std::dec << m_len << " id " << this->m_id;
    taint << " relation : " << enum_strings[rel];
    taint << "source1 = TAINT" << os1.getLength() << " id " << os1.getId();
    taint << std::endl;
    PIN_ReleaseLock(&lock);
    #endif
}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2) 
    : Taint(rel, length, os1, os2)
{
    #if 0
    PIN_GetLock(&lock, 0);
    taint << "Nouvel objet TAINT" << std::dec << m_len << " id " << this->m_id;
    taint << " relation : " << enum_strings[rel];
    taint << "source1 = TAINT" << os1.getLength() << " id " << os1.getId();
    taint << "source2 = TAINT" << os2.getLength() << " id " << os2.getId();
    taint << std::endl;
    PIN_ReleaseLock(&lock);
    #endif
}

template<UINT32 length> 
TaintObject<length>::TaintObject(Relation rel, const ObjectSource &os1, const ObjectSource &os2, const ObjectSource &os3) 
    : Taint(rel, length, os1, os2, os3)
{
    #if 0
    PIN_GetLock(&lock, 0);
    taint << "Nouvel objet TAINT" << std::dec << m_len << " id " << this->m_id;
    taint << " relation : " << enum_strings[rel];
    taint << "source1 = TAINT" << os1.getLength() << " id " << os1.getId();
    taint << "source2 = TAINT" << os2.getLength() << " id " << os2.getId();
    taint << "source3 = TAINT" << os3.getLength() << " id " << os3.getId();
    taint << std::endl;
    PIN_ReleaseLock(&lock);
    #endif
}

template<UINT32 len> TaintObject<len>::~TaintObject() 
{
#if 0
    PIN_GetLock(&lock, 0);
    taint << "destr objet TAINT" << std::dec << m_len << " id " << this->m_id;
    if (this->m_sourceRelation == BYTESOURCE) taint << " (INITIAL)";
    taint << std::endl;
    PIN_ReleaseLock(&lock);
#endif
}

// instanciation des templates utilisés (ou alors il aurait fallu les déclarer dans le .h)
class Taint;
template class TaintObject<1>;
template class TaintObject<8>;
template class TaintObject<16>;
template class TaintObject<32>;
template class TaintObject<64>;
template class TaintObject<128>;