// Lean compiler output
// Module: Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Forms_sgHC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Forms_sgHC___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Forms_sgHC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Forms_sgHC___closed__1;
static lean_once_cell_t lp_tree_Formalism_L2_Forms_sgHC___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Forms_sgHC___closed__2;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_sgHC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_sgT(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Forms_sgHC___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Forms_sgHC___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Forms_sgHC___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_sgHC(lean_object* v_R_7_, lean_object* v_h_8_, lean_object* v_i_9_){
_start:
{
lean_object* v_k_10_; lean_object* v_m_11_; lean_object* v_t_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v_k_10_ = lean_ctor_get(v_R_7_, 1);
lean_inc(v_k_10_);
v_m_11_ = lean_ctor_get(v_R_7_, 2);
lean_inc_n(v_m_11_, 2);
v_t_12_ = lean_ctor_get(v_R_7_, 3);
lean_inc_n(v_t_12_, 2);
lean_dec_ref(v_R_7_);
v___x_13_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_m_11_);
v___x_14_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v_t_12_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_obj_once(&lp_tree_Formalism_L2_Forms_sgHC___closed__0, &lp_tree_Formalism_L2_Forms_sgHC___closed__0_once, _init_lp_tree_Formalism_L2_Forms_sgHC___closed__0);
lean_inc_ref(v___x_14_);
v___x_17_ = l_Rat_add(v___x_14_, v___x_16_);
v___x_18_ = l_Rat_mul(v___x_13_, v___x_17_);
lean_dec_ref(v___x_13_);
v___x_19_ = lean_obj_once(&lp_tree_Formalism_L2_Forms_sgHC___closed__1, &lp_tree_Formalism_L2_Forms_sgHC___closed__1_once, _init_lp_tree_Formalism_L2_Forms_sgHC___closed__1);
v___x_20_ = l_Rat_div(v___x_18_, v___x_19_);
lean_dec_ref(v___x_18_);
v___x_21_ = lean_nat_sub(v_k_10_, v___x_15_);
lean_dec(v_k_10_);
v___x_22_ = lean_nat_dec_lt(v_i_9_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_23_ = lean_nat_sub(v_i_9_, v___x_21_);
lean_dec(v___x_21_);
lean_dec(v_i_9_);
v___x_24_ = lean_nat_add(v_t_12_, v___x_15_);
lean_dec(v_t_12_);
v___x_25_ = lean_nat_div(v___x_23_, v___x_24_);
v___x_26_ = lean_nat_dec_lt(v___x_25_, v_m_11_);
lean_dec(v_m_11_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v___x_25_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
lean_dec_ref(v___x_14_);
lean_dec_ref(v_h_8_);
v___x_27_ = lean_obj_once(&lp_tree_Formalism_L2_Forms_sgHC___closed__2, &lp_tree_Formalism_L2_Forms_sgHC___closed__2_once, _init_lp_tree_Formalism_L2_Forms_sgHC___closed__2);
v___x_28_ = l_Rat_add(v___x_20_, v___x_27_);
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_29_ = lean_nat_mod(v___x_23_, v___x_24_);
lean_dec(v___x_24_);
lean_dec(v___x_23_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_nat_dec_eq(v___x_29_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v_e_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_e_32_ = lean_ctor_get(v_h_8_, 3);
lean_inc_ref(v_e_32_);
lean_dec_ref(v_h_8_);
v___x_33_ = lean_apply_1(v_e_32_, v___x_25_);
v___x_34_ = l_Rat_neg(v___x_33_);
v___x_35_ = l_Rat_sub(v___x_14_, v___x_16_);
v___x_36_ = l_Rat_div(v___x_35_, v___x_19_);
lean_dec_ref(v___x_35_);
v___x_37_ = l_Rat_add(v___x_34_, v___x_36_);
v___x_38_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_29_);
v___x_39_ = l_Rat_sub(v___x_38_, v___x_16_);
v___x_40_ = l_Rat_sub(v___x_37_, v___x_39_);
v___x_41_ = l_Rat_add(v___x_20_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_b_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v___x_29_);
lean_dec_ref(v___x_14_);
v_b_42_ = lean_ctor_get(v_h_8_, 2);
lean_inc_ref(v_b_42_);
lean_dec_ref(v_h_8_);
v___x_43_ = lean_apply_1(v_b_42_, v___x_25_);
v___x_44_ = l_Rat_neg(v___x_43_);
v___x_45_ = l_Rat_add(v___x_20_, v___x_44_);
return v___x_45_;
}
}
}
else
{
lean_object* v_v_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v___x_21_);
lean_dec_ref(v___x_14_);
lean_dec(v_t_12_);
lean_dec(v_m_11_);
v_v_46_ = lean_ctor_get(v_h_8_, 1);
lean_inc_ref(v_v_46_);
lean_dec_ref(v_h_8_);
v___x_47_ = lean_apply_1(v_v_46_, v_i_9_);
v___x_48_ = l_Rat_add(v___x_20_, v___x_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Forms_sgT(lean_object* v_D_49_, lean_object* v_u_50_, lean_object* v_00_u03c4_51_){
_start:
{
lean_object* v_R_52_; lean_object* v_fm_53_; lean_object* v_m_54_; lean_object* v_t_55_; lean_object* v___x_56_; lean_object* v_sg_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___f_64_; 
v_R_52_ = lean_ctor_get(v_D_49_, 0);
lean_inc_ref(v_R_52_);
v_fm_53_ = lean_ctor_get(v_D_49_, 50);
lean_inc_ref(v_fm_53_);
lean_dec_ref(v_D_49_);
v_m_54_ = lean_ctor_get(v_R_52_, 2);
lean_inc(v_m_54_);
v_t_55_ = lean_ctor_get(v_R_52_, 3);
lean_inc(v_t_55_);
lean_dec_ref(v_R_52_);
v___x_56_ = lean_apply_1(v_fm_53_, v_u_50_);
v_sg_57_ = lean_ctor_get(v___x_56_, 15);
lean_inc_ref(v_sg_57_);
lean_dec_ref(v___x_56_);
v___x_58_ = lean_unsigned_to_nat(1u);
v___x_59_ = lean_apply_1(v_sg_57_, v_00_u03c4_51_);
v___x_60_ = lean_nat_add(v_t_55_, v___x_58_);
lean_dec(v_t_55_);
v___x_61_ = lean_nat_mul(v_m_54_, v___x_60_);
lean_dec(v___x_60_);
lean_dec(v_m_54_);
v___x_62_ = lean_nat_shiftr(v___x_61_, v___x_58_);
lean_dec(v___x_61_);
v___x_63_ = lean_nat_to_int(v___x_62_);
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Forms_shW___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_64_, 0, v___x_59_);
lean_closure_set(v___f_64_, 1, v___x_63_);
return v___f_64_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_PrkSmul(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_HermitianForms_LastCoordinateUniformizerVectorSpansOrthogonalLi(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_HermitianForms_PrkSmul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
