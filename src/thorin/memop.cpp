#include "thorin/memop.h"

#include "thorin/literal.h"
#include "thorin/world.h"

namespace thorin {

//------------------------------------------------------------------------------

Alloc::Alloc(Def mem, Type type, Def extra, const std::string& name)
    : MemOp(2, Node_Alloc, mem->world().ptr_type(type), mem, name)
{
    set_op(1, extra);
}

//------------------------------------------------------------------------------

Load::Load(Def mem, Def ptr, const std::string& name)
    : Access(2, Node_Load, ptr->type().as<PtrType>()->referenced_type(), mem, ptr, name)
{}

//------------------------------------------------------------------------------

Store::Store(Def mem, Def ptr, Def value, const std::string& name)
    : Access(3, Node_Store, mem->type(), mem, ptr, name)
{
    set_op(2, value);
}

//------------------------------------------------------------------------------

Enter::Enter(Def mem, const std::string& name)
    : MemOp(1, Node_Enter, mem->world().frame_type(), mem, name)
{}

//------------------------------------------------------------------------------

Leave::Leave(Def mem, Def frame, const std::string& name)
    : MemOp(2, Node_Leave, mem->type(), mem, name)
{
    assert(frame->type().isa<FrameType>());
    set_op(1, frame);
}

//------------------------------------------------------------------------------


MemOp::MemOp(size_t size, NodeKind kind, Type type, Def mem, const std::string& name)
    : PrimOp(size, kind, type, name)
{
    assert(mem->type().isa<MemType>());
    assert(size >= 1);
    set_op(0, mem);
}

//------------------------------------------------------------------------------

MapOp::MapOp(size_t size, NodeKind kind, Type type,
             Def mem, Def ptr, int32_t device, AddressSpace addr_space, const std::string &name)
    : MemOp(size, kind, type, mem, name)
{
    set_op(1, ptr);
}

Map::Map(Def mem, Def ptr, int32_t device, AddressSpace addr_space,
         Def mem_offset, Def mem_size, const std::string &name)
    : MapOp(4, Node_Map, Type(), mem, ptr, device, addr_space, name)
{
    World& w = mem->world();
    set_type(w.tuple_type({ mem->type(),
                            w.ptr_type(ptr->type().as<PtrType>()->referenced_type(),
                            ptr->type().as<PtrType>()->length(), device, addr_space)}));
    set_op(2, mem_offset);
    set_op(3, mem_size);
}

Def Map::extract_mem() const { return world().extract(this, 0); }
Def Map::extract_mapped_ptr() const { return world().extract(this, 1); }

Def Map::mem_out() const {
    auto uses = this->uses();
    assert(1 <= uses.size() && uses.size() <= 2);
    size_t i = uses[0]->type().isa<MemType>() ? 0 : 1;
    assert(uses[i]->isa<Extract>());
    assert(uses[i]->num_uses() == 1);
    return uses[i];
}

Unmap::Unmap(Def mem, Def ptr, int32_t device, AddressSpace addr_space, const std::string &name)
    : MapOp(2, Node_Unmap, mem->type(), mem, ptr, device, addr_space, name)
{}

//------------------------------------------------------------------------------

}
