// Lean compiler output
// Module: Lib.GaloisRep.Main.AttachedRepresentations
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.SchurNorm public import Lib.PadicHodge.Characters public import Lib.Weil.DualPair.FiniteAction
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__0 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__0_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__1 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__1_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__2 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__2_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__3 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__3_value;
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_0),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_1),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value_aux_2),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__4 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__4_value;
static const lean_array_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__5 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__5_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__6 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__6_value;
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_0),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_1),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value_aux_2),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__7 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__7_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__8 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__8_value;
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__9 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__9_value;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__10 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__10_value;
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_0),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_1),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value_aux_2),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__11 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__11_value;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__12;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__13;
static const lean_string_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__14 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__14_value;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__15;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__16;
static const lean_ctor_object lp_GRH_New_GaloisRep_Attached___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(223, 78, 141, 85, 50, 255, 216, 83)}};
static const lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__17 = (const lean_object*)&lp_GRH_New_GaloisRep_Attached___auto__1___closed__17_value;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__18;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__19;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__20;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__21;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__22;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__23;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__24;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__25;
static lean_once_cell_t lp_GRH_New_GaloisRep_Attached___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GaloisRep_Attached___auto__1___closed__26;
LEAN_EXPORT lean_object* lp_GRH_New_GaloisRep_Attached___auto__1;
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__12, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__12_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__12);
v___x_30_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__15(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__14));
v___x_34_ = lean_string_utf8_byte_size(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__16(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__15, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__15_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__15);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__14));
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__18(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_box(0);
v___x_42_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__17));
v___x_43_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__16, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__16_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__16);
v___x_44_ = lean_box(2);
v___x_45_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_43_);
lean_ctor_set(v___x_45_, 2, v___x_42_);
lean_ctor_set(v___x_45_, 3, v___x_41_);
return v___x_45_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__18, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__18_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__18);
v___x_47_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__13, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__13_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__13);
v___x_48_ = lean_array_push(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__20(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__19, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__19_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__19);
v___x_50_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__11));
v___x_51_ = lean_box(2);
v___x_52_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__21(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__20, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__20_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__20);
v___x_54_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__5));
v___x_55_ = lean_array_push(v___x_54_, v___x_53_);
return v___x_55_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__22(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__21, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__21_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__21);
v___x_57_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__9));
v___x_58_ = lean_box(2);
v___x_59_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
return v___x_59_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__23(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__22, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__22_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__22);
v___x_61_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__5));
v___x_62_ = lean_array_push(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__24(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__23, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__23_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__23);
v___x_64_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__7));
v___x_65_ = lean_box(2);
v___x_66_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__25(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__24, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__24_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__24);
v___x_68_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__5));
v___x_69_ = lean_array_push(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__26(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__25, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__25_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__25);
v___x_71_ = ((lean_object*)(lp_GRH_New_GaloisRep_Attached___auto__1___closed__4));
v___x_72_ = lean_box(2);
v___x_73_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_70_);
return v___x_73_;
}
}
static lean_object* _init_lp_GRH_New_GaloisRep_Attached___auto__1(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_obj_once(&lp_GRH_New_GaloisRep_Attached___auto__1___closed__26, &lp_GRH_New_GaloisRep_Attached___auto__1___closed__26_once, _init_lp_GRH_New_GaloisRep_Attached___auto__1___closed__26);
return v___x_74_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_SchurNorm(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Characters(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_FiniteAction(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Main_AttachedRepresentations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_GLn_SchurModule_SchurNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicHodge_Characters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_FiniteAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_GRH_New_GaloisRep_Attached___auto__1 = _init_lp_GRH_New_GaloisRep_Attached___auto__1();
lean_mark_persistent(lp_GRH_New_GaloisRep_Attached___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
