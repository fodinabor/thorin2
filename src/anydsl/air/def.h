#ifndef ANYDSL_AIR_DEF_H
#define ANYDSL_AIR_DEF_H

#include <string>

#include <boost/cstdint.hpp>
#include <boost/unordered_set.hpp>

#include "anydsl/air/airnode.h"

namespace anydsl {

//------------------------------------------------------------------------------

class Lambda;
class Type;
class World;
class Use;
typedef boost::unordered_set<Use*> Uses;

//------------------------------------------------------------------------------

class Def : public AIRNode {
protected:

    Def(IndexKind index, const Type* type)
        : AIRNode(index) 
        , type_(type)
    {}

public:

    //virtual ~Def() { anydsl_assert(uses_.empty(), "there are still uses pointing to this def"); }
    virtual ~Def() { /* TODO assertion above is useful */ }

    /**
     * Manually adds given \p Use object to the list of uses of this \p Def.
     * use->def() must already point to \p this .
     */
    void registerUse(Use* use);

    /**
     * Manually removes given \p Use object from the list of uses of this \p Def.
     * use->def() must point to \p this , but should be unset right after the call to this function
     */
    void unregisterUse(Use* use);

    const Uses& uses() const { return uses_; }
    const Type* type() const { return type_; }
    World& world() const;

protected:

    void setType(const Type* type) { type_ = type; }

private:

    const Type* type_;
    Uses uses_;
};

//------------------------------------------------------------------------------

class Param : public Def {
private:

    Param(Lambda* parent, const Type* type)
        : Def(Index_Param, type)
        , parent_(parent)
    {}

    const Lambda* parent() const { return parent_; }

private:

    Lambda* parent_;

    friend class Lambda;
};

//------------------------------------------------------------------------------


class Value : public Def {
protected:

    Value(IndexKind index, const Type* type)
        : Def(index, type)
    {}
};

struct ValueNumber {
    uint8_t index;
    uintptr_t op1;
    uintptr_t op2;

    ValueNumber() {}
    ValueNumber(IndexKind index)
        : index(index)
        , op1(0)
        , op2(0)
    {}
    ValueNumber(IndexKind index, const void* p)
        : index(index)
        , op1(uintptr_t(p))
        , op2(uintptr_t(0))
    {}
    ValueNumber(IndexKind index, const void* p1, const void* p2) 
        : index(index)
        , op1(uintptr_t(p1))
        , op2(uintptr_t(p2))
    {}

    bool operator == (const ValueNumber& vn) const {
        return index == vn.index && op1 == vn.op1 && op2 == vn.op2;
    }
    bool operator != (const ValueNumber& vn) const {
        return index != vn.index || op1 != vn.op1 || op2 != vn.op2;
    }
};

inline size_t hash_value(const ValueNumber& vn) {
    return 0;
}

//------------------------------------------------------------------------------

class PrimOp : public Value {
public:

    PrimOpKind primOpKind() const { return (PrimOpKind) index(); }

protected:

    PrimOp(IndexKind index, const Type* type)
        : Value(index, type)
    {}
};

//------------------------------------------------------------------------------

} // namespace anydsl

#endif // ANYDSL_AIR_DEF_H
