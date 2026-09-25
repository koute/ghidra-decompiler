use super::{Datatype, TypeField, TypeId, TypeKind, TypeMetatype, types_of, types_of_mut};
use crate::architecture::Architecture;
use crate::error::Result;
use crate::funcdata::Funcdata;
use crate::op::OpId;
use crate::opcodes::OpCode;
use crate::unionresolve::{ResolvedUnion, ScoreUnionFields};

impl Datatype {
    pub fn find_truncation(
        ct: TypeId,
        off: i64,
        sz: i32,
        op: OpId,
        slot: i32,
        newoff: &mut i64,
        data: &Funcdata,
        glb: &Architecture,
    ) -> Option<TypeField> {
        let types = types_of(glb);
        let dt = types.get(ct);
        match &dt.kind {
            TypeKind::Struct(fields) => {
                let index = dt.get_field_iter(off as i32, types);
                if index < 0 {
                    return None;
                }
                let curfield = &fields.field[index as usize];
                let noff = (off - curfield.offset as i64) as i32;
                if noff + sz > types.get(curfield.tp).get_size() {
                    return None;
                }
                *newoff = noff as i64;
                Some(curfield.clone())
            }
            TypeKind::Union(_) => {
                let res = data.get_union_resolution(ct, op, slot, glb)?;
                if res.get_field_num() < 0 {
                    return None;
                }
                let field = dt.get_field(res.get_field_num());
                *newoff = off - field.offset as i64;
                if *newoff + sz as i64 > types.get(field.tp).get_size() as i64 {
                    return None;
                }
                Some(field.clone())
            }
            TypeKind::PartialUnion(partial) => Datatype::find_truncation(
                partial.container,
                off + partial.offset as i64,
                sz,
                op,
                slot,
                newoff,
                data,
                glb,
            ),
            _ => None,
        }
    }

    pub fn resolve_in_flow(
        ct: TypeId,
        op: OpId,
        slot: i32,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<TypeId> {
        let dt = types_of(glb).get(ct);
        match &dt.kind {
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => {
                let ptrto = dt.get_ptr_to();
                if types_of(glb).get(ptrto).get_metatype() != TypeMetatype::Union {
                    return Ok(ct);
                }
                if let Some(res) = data.get_union_field(ct, op, slot, glb) {
                    return Ok(res.get_datatype());
                }
                let addr = data.op(op).get_addr().clone();
                let address_field = data
                    .get_address_based_union_field(ct, &addr, slot, glb)
                    .map(|res| res.get_field_num());
                if let Some(field_num) = address_field {
                    let resolve = ResolvedUnion::new_field(ct, field_num, types_of_mut(glb))?;
                    data.set_union_field(ct, op, slot, &resolve, glb);
                    return Ok(resolve.get_datatype());
                }
                let score_fields = ScoreUnionFields::new(data, glb, ct, op, slot)?;
                data.set_union_field(ct, op, slot, score_fields.get_result(), glb);
                Ok(score_fields.get_result().get_datatype())
            }
            TypeKind::Array(_) | TypeKind::Struct(_) => {
                if let Some(res) = data.get_union_field(ct, op, slot, glb) {
                    return Ok(res.get_datatype());
                }
                let field_num = Datatype::score_single_component(ct, op, slot, data, glb);
                let comp_fill = ResolvedUnion::new_field(ct, field_num, types_of_mut(glb))?;
                data.set_union_field(ct, op, slot, &comp_fill, glb);
                Ok(comp_fill.get_datatype())
            }
            TypeKind::Union(_) => {
                if let Some(res) = data.get_union_field(ct, op, slot, glb) {
                    return Ok(res.get_datatype());
                }
                let addr = data.op(op).get_addr().clone();
                let address_res = data.get_address_based_union_field(ct, &addr, slot, glb).cloned();
                if let Some(res) = address_res {
                    let resolve = ResolvedUnion::new_field(ct, res.get_field_num(), types_of_mut(glb))?;
                    data.set_union_field(ct, op, slot, &res, glb);
                    return Ok(resolve.get_datatype());
                }
                let score_fields = ScoreUnionFields::new(data, glb, ct, op, slot)?;
                data.set_union_field(ct, op, slot, score_fields.get_result(), glb);
                Ok(score_fields.get_result().get_datatype())
            }
            TypeKind::PartialUnion(partial) => {
                if let Some(res) = data.get_union_field(ct, op, slot, glb) {
                    return Ok(res.get_datatype());
                }
                let size = dt.get_size();
                let stripped = partial.stripped;
                let mut cur_type = Some(partial.container);
                let mut cur_off = partial.offset as i64;
                while let Some(cur) = cur_type {
                    let cur_dt = types_of(glb).get(cur);
                    if cur_dt.get_size() <= size {
                        break;
                    }
                    if cur_dt.get_metatype() == TypeMetatype::PartialUnion {
                        cur_off += cur_dt.get_offset() as i64;
                        let parent_union = cur_dt.get_parent_union();
                        let mut new_off = 0i64;
                        let field =
                            Datatype::resolve_truncation(parent_union, cur_off, op, slot, &mut new_off, data, glb)?;
                        cur_type = None;
                        if let Some(field) = field {
                            cur_type = types_of_mut(glb).get_exact_piece(field.tp, cur_off as i32, size)?;
                        }
                        cur_off = 0;
                    } else if cur_dt.get_metatype() == TypeMetatype::Union {
                        let mut new_off = cur_off;
                        let field = Datatype::resolve_truncation(cur, cur_off, op, slot, &mut new_off, data, glb)?;
                        cur_off = new_off;
                        cur_type = None;
                        if let Some(field) = field {
                            cur_type = types_of_mut(glb).get_exact_piece(field.tp, cur_off as i32, size)?;
                        }
                        cur_off = 0;
                    } else {
                        cur_type = None;
                        break;
                    }
                }
                let result = match cur_type {
                    Some(cur) if types_of(glb).get(cur).get_size() == size => cur,
                    _ => stripped,
                };
                data.update_union_field(ct, op, slot, result, glb);
                Ok(result)
            }
            _ => Ok(ct),
        }
    }

    pub fn find_resolve(ct: TypeId, op: OpId, slot: i32, data: &Funcdata, glb: &Architecture) -> TypeId {
        let types = types_of(glb);
        let dt = types.get(ct);
        match &dt.kind {
            TypeKind::Pointer(_) | TypeKind::PointerRel(_) => {
                if types.get(dt.get_ptr_to()).get_metatype() == TypeMetatype::Union
                    && let Some(res) = data.get_union_field(ct, op, slot, glb)
                {
                    return res.get_datatype();
                }
                ct
            }
            TypeKind::Array(array) => match data.get_union_field(ct, op, slot, glb) {
                Some(res) => res.get_datatype(),
                None => array.arrayof.expect("array without element type"),
            },
            TypeKind::Struct(fields) => match data.get_union_field(ct, op, slot, glb) {
                Some(res) => res.get_datatype(),
                None => fields.field[0].tp,
            },
            TypeKind::Union(_) => match data.get_union_field(ct, op, slot, glb) {
                Some(res) => res.get_datatype(),
                None => ct,
            },
            TypeKind::PartialUnion(partial) => match data.get_union_field(ct, op, slot, glb) {
                Some(res) => res.get_datatype(),
                None => partial.stripped,
            },
            _ => ct,
        }
    }

    pub fn resolve_truncation(
        ct: TypeId,
        offset: i64,
        op: OpId,
        slot: i32,
        newoff: &mut i64,
        data: &mut Funcdata,
        glb: &mut Architecture,
    ) -> Result<Option<TypeField>> {
        let dt = types_of(glb).get(ct);
        match &dt.kind {
            TypeKind::Union(_) => {
                let mut res = data.get_union_resolution(ct, op, slot, glb).cloned();
                if res.is_none() {
                    let addr = data.op(op).get_addr().clone();
                    res = data.get_address_based_union_field(ct, &addr, slot, glb).cloned();
                    if let Some(address_res) = &res {
                        data.set_union_field(ct, op, slot, address_res, glb);
                    }
                }
                if let Some(res) = res {
                    if res.get_field_num() >= 0 {
                        let field = types_of(glb).get(ct).get_field(res.get_field_num()).clone();
                        *newoff = offset - field.offset as i64;
                        return Ok(Some(field));
                    }
                } else if data.op(op).code() == OpCode::Subpiece && slot == 1 {
                    let score_fields = ScoreUnionFields::new_offset(data, glb, ct, offset as i32, op)?;
                    data.set_union_field(ct, op, slot, score_fields.get_result(), glb);
                    let field_num = score_fields.get_result().get_field_num();
                    if field_num >= 0 {
                        *newoff = 0;
                        return Ok(Some(types_of(glb).get(ct).get_field(field_num).clone()));
                    }
                } else {
                    let score_fields = ScoreUnionFields::new_offset_slot(data, glb, ct, offset as i32, op, slot)?;
                    data.set_union_field(ct, op, slot, score_fields.get_result(), glb);
                    let field_num = score_fields.get_result().get_field_num();
                    if field_num >= 0 {
                        let field = types_of(glb).get(ct).get_field(field_num).clone();
                        *newoff = offset - field.offset as i64;
                        return Ok(Some(field));
                    }
                }
                Ok(None)
            }
            TypeKind::PartialUnion(partial) => {
                let container = partial.container;
                let partial_offset = partial.offset as i64;
                Datatype::resolve_truncation(container, offset + partial_offset, op, slot, newoff, data, glb)
            }
            _ => Ok(None),
        }
    }

    pub fn score_single_component(parent: TypeId, op: OpId, slot: i32, data: &mut Funcdata, glb: &Architecture) -> i32 {
        let opc = data.op(op).code();
        if opc == OpCode::Copy || opc == OpCode::Indirect {
            let vn = if slot == 0 {
                data.op(op).get_out()
            } else {
                Some(data.op(op).get_in(0))
            };
            if let Some(vn) = vn {
                let vn_data = data.vn(vn);
                if vn_data.is_type_lock() && vn_data.get_type() == parent {
                    return -1;
                }
            }
        } else if (opc == OpCode::Load && slot == -1) || (opc == OpCode::Store && slot == 2) {
            let vn = data.op(op).get_in(1);
            if data.vn(vn).is_type_lock() {
                let ct = data.vn_get_type_read_facing(vn, op, glb);
                let ct_dt = types_of(glb).get(ct);
                if ct_dt.get_metatype() == TypeMetatype::Ptr && ct_dt.get_ptr_to() == parent {
                    return -1;
                }
            }
        } else if data.op(op).is_call()
            && let Some(fc) = data.get_call_specs_op(op)
        {
            let spec = data.call_spec_mut(fc);
            let mut param = None;
            if slot >= 1 && spec.is_input_locked(glb) {
                param = spec.get_param(slot - 1, glb).map(|param| param.get_type(glb));
            } else if slot < 0 && spec.is_output_locked(glb) {
                param = spec.get_output_ref().map(|param| param.get_type(glb));
            }
            if param == Some(parent) {
                return -1;
            }
        }
        0
    }
}
