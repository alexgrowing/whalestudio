// Lean compiler output
// Module: Lib.GLn.Branching.NormBound
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.LeadingRows
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_Fin_castLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_submatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_detRowAlternating___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fin_cycleRange(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_GL_frontPermutation___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_GL_frontPermutation___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_GL_frontPermutation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_frontPermutation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_GL_extremalFilling___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_GL_extremalFilling___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_GL_extremalFilling___redArg___closed__0 = (const lean_object*)&lp_GRH_New_GL_extremalFilling___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_GL_frontPermutation___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_refl___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_frontPermutation(lean_object* v_N_2_, lean_object* v_p_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_p_3_, v_N_2_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
lean_dec(v_N_2_);
v___x_5_ = lean_obj_once(&lp_GRH_New_GL_frontPermutation___closed__0, &lp_GRH_New_GL_frontPermutation___closed__0_once, _init_lp_GRH_New_GL_frontPermutation___closed__0);
return v___x_5_;
}
else
{
lean_object* v___x_6_; 
v___x_6_ = lp_mathlib_Fin_cycleRange(v_N_2_, v_p_3_);
return v___x_6_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_frontPermutation___boxed(lean_object* v_N_7_, lean_object* v_p_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_GRH_New_GL_frontPermutation(v_N_7_, v_p_8_);
lean_dec(v_p_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___lam__0(lean_object* v_s_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_s_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___lam__0___boxed(lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_GL_extremalFilling___redArg___lam__0(v_s_13_);
lean_dec(v_s_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg(lean_object* v_inst_16_, lean_object* v_p_17_, lean_object* v_00_u03ba_x27_18_, lean_object* v_00_u03c4_19_, lean_object* v_k_20_, lean_object* v_j_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
lean_inc_n(v_00_u03c4_19_, 2);
v___x_22_ = lean_apply_1(v_p_17_, v_00_u03c4_19_);
v___x_23_ = lean_nat_add(v___x_22_, v_k_20_);
v___x_24_ = lean_apply_2(v_00_u03ba_x27_18_, v_00_u03c4_19_, v___x_23_);
v___x_25_ = lean_nat_dec_lt(v_j_21_, v___x_24_);
lean_dec(v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___f_26_; 
lean_dec(v___x_22_);
lean_dec(v_k_20_);
lean_dec(v_00_u03c4_19_);
lean_dec(v_inst_16_);
v___f_26_ = ((lean_object*)(lp_GRH_New_GL_extremalFilling___redArg___closed__0));
return v___f_26_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_27_ = lean_apply_1(v_inst_16_, v_00_u03c4_19_);
v___x_28_ = l_List_lengthTR___redArg(v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_nat_sub(v___x_28_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v___x_28_);
v___x_30_ = l_List_finRange(v___x_29_);
v___x_31_ = l_List_lengthTR___redArg(v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_alloc_closure((void*)(l_Fin_castLE___boxed), 4, 3);
lean_closure_set(v___x_32_, 0, v_k_20_);
lean_closure_set(v___x_32_, 1, v___x_31_);
lean_closure_set(v___x_32_, 2, lean_box(0));
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___redArg___boxed(lean_object* v_inst_33_, lean_object* v_p_34_, lean_object* v_00_u03ba_x27_35_, lean_object* v_00_u03c4_36_, lean_object* v_k_37_, lean_object* v_j_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_GRH_New_GL_extremalFilling___redArg(v_inst_33_, v_p_34_, v_00_u03ba_x27_35_, v_00_u03c4_36_, v_k_37_, v_j_38_);
lean_dec(v_j_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling(lean_object* v_00_u03a6_40_, lean_object* v_n_41_, lean_object* v_inst_42_, lean_object* v_p_43_, lean_object* v_00_u03ba_u2080_44_, lean_object* v_00_u03ba_x27_45_, lean_object* v_00_u03c4_46_, lean_object* v_k_47_, lean_object* v_j_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_GRH_New_GL_extremalFilling___redArg(v_inst_42_, v_p_43_, v_00_u03ba_x27_45_, v_00_u03c4_46_, v_k_47_, v_j_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_extremalFilling___boxed(lean_object* v_00_u03a6_50_, lean_object* v_n_51_, lean_object* v_inst_52_, lean_object* v_p_53_, lean_object* v_00_u03ba_u2080_54_, lean_object* v_00_u03ba_x27_55_, lean_object* v_00_u03c4_56_, lean_object* v_k_57_, lean_object* v_j_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_GRH_New_GL_extremalFilling(v_00_u03a6_50_, v_n_51_, v_inst_52_, v_p_53_, v_00_u03ba_u2080_54_, v_00_u03ba_x27_55_, v_00_u03c4_56_, v_k_57_, v_j_58_);
lean_dec(v_j_58_);
lean_dec_ref(v_00_u03ba_u2080_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong___redArg___lam__0(lean_object* v___x_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_toFun_62_; lean_object* v___x_63_; 
v_toFun_62_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_toFun_62_);
lean_dec_ref(v___x_60_);
v___x_63_ = lean_apply_1(v_toFun_62_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong___redArg(lean_object* v_inst_64_, lean_object* v_k_65_, lean_object* v_e_66_, lean_object* v_z_67_, lean_object* v_h_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_29__overap_76_; lean_object* v___x_77_; 
lean_inc_n(v_h_68_, 2);
v___x_69_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_69_, 0, v_h_68_);
v___x_70_ = l_List_finRange(v_h_68_);
v___x_71_ = lp_mathlib_Equiv_symm___redArg(v_e_66_);
v___f_72_ = lean_alloc_closure((void*)(lp_GRH_New_GL_leadingMinorAlong___redArg___lam__0), 2, 1);
lean_closure_set(v___f_72_, 0, v___x_71_);
v___x_73_ = lean_alloc_closure((void*)(l_Fin_castLE___boxed), 4, 3);
lean_closure_set(v___x_73_, 0, v_h_68_);
lean_closure_set(v___x_73_, 1, v_k_65_);
lean_closure_set(v___x_73_, 2, lean_box(0));
v___x_74_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, lean_box(0));
lean_closure_set(v___x_74_, 2, lean_box(0));
lean_closure_set(v___x_74_, 3, v___f_72_);
lean_closure_set(v___x_74_, 4, v___x_73_);
lean_inc_ref(v___x_74_);
v___x_75_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_submatrix), 10, 8);
lean_closure_set(v___x_75_, 0, lean_box(0));
lean_closure_set(v___x_75_, 1, lean_box(0));
lean_closure_set(v___x_75_, 2, lean_box(0));
lean_closure_set(v___x_75_, 3, lean_box(0));
lean_closure_set(v___x_75_, 4, lean_box(0));
lean_closure_set(v___x_75_, 5, v_z_67_);
lean_closure_set(v___x_75_, 6, v___x_74_);
lean_closure_set(v___x_75_, 7, v___x_74_);
v___x_29__overap_76_ = lp_mathlib_Matrix_detRowAlternating___redArg(v___x_69_, v___x_70_, v_inst_64_);
v___x_77_ = lean_apply_1(v___x_29__overap_76_, v___x_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_GL_leadingMinorAlong(lean_object* v_R_78_, lean_object* v_inst_79_, lean_object* v_m_80_, lean_object* v_k_81_, lean_object* v_e_82_, lean_object* v_z_83_, lean_object* v_h_84_, lean_object* v_h__le_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_GRH_New_GL_leadingMinorAlong___redArg(v_inst_79_, v_k_81_, v_e_82_, v_z_83_, v_h_84_);
return v___x_86_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_LeadingRows(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GLn_Branching_NormBound(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_LeadingRows(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
