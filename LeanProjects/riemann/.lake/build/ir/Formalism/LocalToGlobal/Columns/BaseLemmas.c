// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.BaseLemmas
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
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
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_pOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_bAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_vb(lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_Fields_conjO(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_sh___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_sh___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_sh___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_sh___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sh(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_hcV(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_hcV___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_conjOEquiv(lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_sh(lean_object* v_R_5_){
_start:
{
lean_object* v_m_6_; lean_object* v_t_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_m_6_ = lean_ctor_get(v_R_5_, 2);
lean_inc(v_m_6_);
v_t_7_ = lean_ctor_get(v_R_5_, 3);
lean_inc(v_t_7_);
lean_dec_ref(v_R_5_);
v___x_8_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_m_6_);
v___x_9_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_7_);
v___x_10_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sh___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sh___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__0);
v___x_11_ = l_Rat_add(v___x_9_, v___x_10_);
v___x_12_ = l_Rat_mul(v___x_8_, v___x_11_);
lean_dec_ref(v___x_8_);
v___x_13_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sh___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sh___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__1);
v___x_14_ = l_Rat_div(v___x_12_, v___x_13_);
lean_dec_ref(v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_hcV(lean_object* v_R_15_, lean_object* v_S_16_, lean_object* v_j_17_, lean_object* v_n_18_){
_start:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = lp_tree_Formalism_L2_Col_RowPar_pOf(v_R_15_, v_j_17_);
v___x_20_ = lean_nat_dec_lt(v_n_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v_t_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_t_21_ = lean_ctor_get(v_R_15_, 3);
v___x_22_ = lean_nat_add(v___x_19_, v_t_21_);
v___x_23_ = lean_nat_dec_lt(v_n_18_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_19_);
v___x_24_ = lean_nat_sub(v_n_18_, v___x_22_);
lean_dec(v___x_22_);
lean_dec(v_n_18_);
v___x_25_ = lean_nat_add(v_j_17_, v___x_24_);
lean_dec(v___x_24_);
v___x_26_ = lp_tree_Formalism_L2_Col_RowPar_bAt(v_R_15_, v_S_16_, v___x_25_);
lean_dec_ref(v_R_15_);
v___x_27_ = l_Rat_neg(v___x_26_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc(v_t_21_);
lean_dec(v___x_22_);
v___x_28_ = lean_unsigned_to_nat(1u);
v___x_29_ = lean_nat_sub(v_j_17_, v___x_28_);
v___x_30_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_15_, v_S_16_, v___x_29_);
lean_dec_ref(v_R_15_);
v___x_31_ = l_Rat_neg(v___x_30_);
v___x_32_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_21_);
v___x_33_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sh___closed__0, &lp_tree_Formalism_L2_Col_RowPar_sh___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__0);
v___x_34_ = l_Rat_sub(v___x_32_, v___x_33_);
v___x_35_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_sh___closed__1, &lp_tree_Formalism_L2_Col_RowPar_sh___closed__1_once, _init_lp_tree_Formalism_L2_Col_RowPar_sh___closed__1);
v___x_36_ = l_Rat_div(v___x_34_, v___x_35_);
lean_dec_ref(v___x_34_);
v___x_37_ = l_Rat_add(v___x_31_, v___x_36_);
v___x_38_ = lean_nat_sub(v_n_18_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v_n_18_);
v___x_39_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_38_);
v___x_40_ = l_Rat_sub(v___x_37_, v___x_39_);
return v___x_40_;
}
}
else
{
lean_object* v___x_41_; 
lean_dec(v___x_19_);
v___x_41_ = lp_tree_Formalism_L2_Col_RowPar_vb(v_R_15_, v_S_16_, v_n_18_);
lean_dec_ref(v_R_15_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_hcV___boxed(lean_object* v_R_42_, lean_object* v_S_43_, lean_object* v_j_44_, lean_object* v_n_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_L2_Col_RowPar_hcV(v_R_42_, v_S_43_, v_j_44_, v_n_45_);
lean_dec(v_j_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__0(lean_object* v_f_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_apply_1(v_f_47_, v___y_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__1(lean_object* v_g_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_apply_1(v_g_50_, v___y_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg(lean_object* v_f_53_, lean_object* v_g_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; 
v___f_55_ = lean_alloc_closure((void*)(lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_f_53_);
v___f_56_ = lean_alloc_closure((void*)(lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg___lam__1), 2, 1);
lean_closure_set(v___f_56_, 0, v_g_54_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___f_55_);
lean_ctor_set(v___x_57_, 1, v___f_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0(lean_object* v_X_58_, lean_object* v_f_59_, lean_object* v_g_60_, lean_object* v_h_u2081_61_, lean_object* v_h_u2082_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg(v_f_59_, v_g_60_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___boxed(lean_object* v_X_64_, lean_object* v_f_65_, lean_object* v_g_66_, lean_object* v_h_u2081_67_, lean_object* v_h_u2082_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0(v_X_64_, v_f_65_, v_g_66_, v_h_u2081_67_, v_h_u2082_68_);
lean_dec_ref(v_X_64_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Fields_conjOEquiv(lean_object* v_X_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lp_tree_Formalism_L2_Col_Fields_conjO(v_X_70_);
lean_inc(v___x_71_);
v___x_72_ = lp_tree_RingEquiv_ofRingHom___at___00Formalism_L2_Col_Fields_conjOEquiv_spec__0___redArg(v___x_71_, v___x_71_);
return v___x_72_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_BaseLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
