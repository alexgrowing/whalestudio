// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementC public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
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
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
extern lean_object* lp_mathlib_Rat_instDivisionRing;
lean_object* lp_mathlib_Ring_toNonAssocRing___redArg(lean_object*);
lean_object* lp_mathlib_Int_castRingHom___redArg(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
static lean_once_cell_t lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0;
static lean_once_cell_t lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_UG_P_easyc__fstAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd___closed__0 = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__fstAdd___closed__0_value;
LEAN_EXPORT const lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__fstAdd___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Algebra_linearMap___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__0;
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0(lean_object*);
static const lean_closure_object lp_tree_Formalism_UG_P_easyc__fst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_UG_P_easyc__fstAdd___closed__0_value)} };
static const lean_object* lp_tree_Formalism_UG_P_easyc__fst___closed__0 = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__fst___closed__0_value;
LEAN_EXPORT const lean_object* lp_tree_Formalism_UG_P_easyc__fst = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__fst___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__0;
static const lean_closure_object lp_tree_Formalism_UG_P_easyc__swap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_UG_P_easyc__swap___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__1 = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__swap___closed__1_value;
static const lean_closure_object lp_tree_Formalism_UG_P_easyc__swap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_UG_P_easyc__swap___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__2 = (const lean_object*)&lp_tree_Formalism_UG_P_easyc__swap___closed__2_value;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__3;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__4;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__5;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__6;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__7;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__8;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__9;
static lean_once_cell_t lp_tree_Formalism_UG_P_easyc__swap___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_easyc__swap___closed__10;
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap;
static lean_object* _init_lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_ZMod_instField___redArg(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0, &lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0_once, _init_lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__0);
v___x_4_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_toRing_7_; lean_object* v___x_8_; lean_object* v_toIntCast_9_; lean_object* v___x_10_; 
v___x_6_ = lean_obj_once(&lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1, &lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1_once, _init_lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1___closed__1);
v_toRing_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_toRing_7_);
v___x_8_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_7_);
v_toIntCast_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_toIntCast_9_);
lean_dec_ref(v___x_8_);
v___x_10_ = lean_apply_1(v_toIntCast_9_, v_a_5_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0(lean_object* v___x_11_, lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_num_16_; lean_object* v___x_17_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_mod(v___x_13_, v___x_11_);
v___x_15_ = lean_apply_1(v_x_12_, v___x_14_);
v_num_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_num_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lp_tree_Int_cast___at___00Formalism_UG_P_easyc__fstAdd_spec__1(v_num_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0___boxed(lean_object* v___x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_UG_P_easyc__fstAdd___lam__0(v___x_18_, v_x_19_);
lean_dec(v___x_18_);
return v_res_20_;
}
}
static lean_object* _init_lp_tree_Algebra_linearMap___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__0(void){
_start:
{
lean_object* v___x_24_; lean_object* v_toRing_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = lp_mathlib_Rat_instDivisionRing;
v_toRing_25_ = lean_ctor_get(v___x_24_, 0);
v___x_26_ = lp_mathlib_Ring_toNonAssocRing___redArg(v_toRing_25_);
v___x_27_ = lp_mathlib_Int_castRingHom___redArg(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__2(lean_object* v_n_28_, lean_object* v_I_29_, lean_object* v_p_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_pi___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__2___boxed(lean_object* v_n_32_, lean_object* v_I_33_, lean_object* v_p_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_tree_Submodule_pi___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__2(v_n_32_, v_I_33_, v_p_34_);
lean_dec_ref(v_p_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_u2081_u2082_36_, lean_object* v_inst_37_, lean_object* v_f_38_, lean_object* v_p_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_u2081_u2082_41_, lean_object* v_inst_42_, lean_object* v_f_43_, lean_object* v_p_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Submodule_map___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__3(v_00_u03c3_u2081_u2082_41_, v_inst_42_, v_f_43_, v_p_44_);
lean_dec_ref(v_f_43_);
lean_dec_ref(v_00_u03c3_u2081_u2082_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Submodule_copy___at___00LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1_spec__4(lean_object* v_p_46_, lean_object* v_s_47_, lean_object* v_hs_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___redArg(lean_object* v_00_u03c4_u2081_u2082_50_, lean_object* v_f_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_box(0);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___redArg___boxed(lean_object* v_00_u03c4_u2081_u2082_53_, lean_object* v_f_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___redArg(v_00_u03c4_u2081_u2082_53_, v_f_54_);
lean_dec_ref(v_f_54_);
lean_dec_ref(v_00_u03c4_u2081_u2082_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0___lam__0(lean_object* v_x_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0___lam__0___boxed(lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0___lam__0(v_x_58_);
lean_dec(v_x_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0(lean_object* v_n_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1(lean_object* v_00_u03c4_u2081_u2082_62_, lean_object* v_inst_63_, lean_object* v_f_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1___boxed(lean_object* v_00_u03c4_u2081_u2082_66_, lean_object* v_inst_67_, lean_object* v_f_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_LinearMap_range___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__1(v_00_u03c4_u2081_u2082_66_, v_inst_67_, v_f_68_);
lean_dec_ref(v_f_68_);
lean_dec_ref(v_00_u03c4_u2081_u2082_66_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0___lam__0(lean_object* v_f_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_apply_1(v_f_70_, v___y_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0(lean_object* v_f_73_){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = lean_alloc_closure((void*)(lp_tree_AddMonoidHom_toIntLinearMap___at___00Formalism_UG_P_easyc__fst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_74_, 0, v_f_73_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__0(lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__0___boxed(lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_tree_Formalism_UG_P_easyc__swap___lam__0(v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec(v___y_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__1(lean_object* v___y_83_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__1___boxed(lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_tree_Formalism_UG_P_easyc__swap___lam__1(v___y_84_);
lean_dec(v___y_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__2(lean_object* v___x_86_, lean_object* v___f_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Fin_cases___redArg(v___x_86_, v___f_87_, v___y_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed(lean_object* v___x_90_, lean_object* v___f_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_UG_P_easyc__swap___lam__2(v___x_90_, v___f_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___x_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__4(lean_object* v___f_94_, lean_object* v___f_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_102__overap_98_; lean_object* v___x_99_; 
v___x_102__overap_98_ = l_Fin_cases___redArg(v___f_94_, v___f_95_, v___y_96_);
v___x_99_ = lean_apply_1(v___x_102__overap_98_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_easyc__swap___lam__4___boxed(lean_object* v___f_100_, lean_object* v___f_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_tree_Formalism_UG_P_easyc__swap___lam__4(v___f_100_, v___f_101_, v___y_102_, v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___f_100_);
return v_res_104_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__0(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_105_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__3(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__4(void){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___f_112_; 
v___f_110_ = ((lean_object*)(lp_tree_Formalism_UG_P_easyc__swap___closed__2));
v___x_111_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__3, &lp_tree_Formalism_UG_P_easyc__swap___closed__3_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__3);
v___f_112_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed), 3, 2);
lean_closure_set(v___f_112_, 0, v___x_111_);
lean_closure_set(v___f_112_, 1, v___f_110_);
return v___f_112_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__5(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__6(void){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___f_117_; 
v___f_115_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__4, &lp_tree_Formalism_UG_P_easyc__swap___closed__4_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__4);
v___x_116_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__5, &lp_tree_Formalism_UG_P_easyc__swap___closed__5_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__5);
v___f_117_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed), 3, 2);
lean_closure_set(v___f_117_, 0, v___x_116_);
lean_closure_set(v___f_117_, 1, v___f_115_);
return v___f_117_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__7(void){
_start:
{
lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___f_120_; 
v___f_118_ = ((lean_object*)(lp_tree_Formalism_UG_P_easyc__swap___closed__1));
v___f_119_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__6, &lp_tree_Formalism_UG_P_easyc__swap___closed__6_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__6);
v___f_120_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__4___boxed), 4, 2);
lean_closure_set(v___f_120_, 0, v___f_119_);
lean_closure_set(v___f_120_, 1, v___f_118_);
return v___f_120_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__8(void){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___f_123_; 
v___f_121_ = ((lean_object*)(lp_tree_Formalism_UG_P_easyc__swap___closed__2));
v___x_122_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__5, &lp_tree_Formalism_UG_P_easyc__swap___closed__5_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__5);
v___f_123_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed), 3, 2);
lean_closure_set(v___f_123_, 0, v___x_122_);
lean_closure_set(v___f_123_, 1, v___f_121_);
return v___f_123_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__9(void){
_start:
{
lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___f_126_; 
v___f_124_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__8, &lp_tree_Formalism_UG_P_easyc__swap___closed__8_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__8);
v___x_125_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__3, &lp_tree_Formalism_UG_P_easyc__swap___closed__3_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__3);
v___f_126_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__2___boxed), 3, 2);
lean_closure_set(v___f_126_, 0, v___x_125_);
lean_closure_set(v___f_126_, 1, v___f_124_);
return v___f_126_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap___closed__10(void){
_start:
{
lean_object* v___f_127_; lean_object* v___f_128_; lean_object* v___f_129_; 
v___f_127_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__7, &lp_tree_Formalism_UG_P_easyc__swap___closed__7_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__7);
v___f_128_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__9, &lp_tree_Formalism_UG_P_easyc__swap___closed__9_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__9);
v___f_129_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_easyc__swap___lam__4___boxed), 4, 2);
lean_closure_set(v___f_129_, 0, v___f_128_);
lean_closure_set(v___f_129_, 1, v___f_127_);
return v___f_129_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_easyc__swap(void){
_start:
{
lean_object* v___x_130_; lean_object* v_toFun_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_130_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__0, &lp_tree_Formalism_UG_P_easyc__swap___closed__0_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__0);
v_toFun_131_ = lean_ctor_get(v___x_130_, 0);
v___f_132_ = lean_obj_once(&lp_tree_Formalism_UG_P_easyc__swap___closed__10, &lp_tree_Formalism_UG_P_easyc__swap___closed__10_once, _init_lp_tree_Formalism_UG_P_easyc__swap___closed__10);
lean_inc(v_toFun_131_);
v___x_133_ = lean_apply_1(v_toFun_131_, v___f_132_);
lean_inc_ref(v___x_133_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
return v___x_134_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementC(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LevelSubgroupFiniteAdelicStandard(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tree_Algebra_linearMap___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__0 = _init_lp_tree_Algebra_linearMap___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__0();
lean_mark_persistent(lp_tree_Algebra_linearMap___at___00Formalism_UG_stdLat___at___00Formalism_UG_P_easyc__fstAdd_spec__0_spec__0);
lp_tree_Formalism_UG_P_easyc__swap = _init_lp_tree_Formalism_UG_P_easyc__swap();
lean_mark_persistent(lp_tree_Formalism_UG_P_easyc__swap);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
