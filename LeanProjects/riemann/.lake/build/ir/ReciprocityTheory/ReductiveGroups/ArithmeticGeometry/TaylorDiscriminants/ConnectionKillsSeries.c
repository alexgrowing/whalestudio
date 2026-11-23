// Lean compiler output
// Module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
// Imports: public import Init public meta import Init public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___closed__0 = (const lean_object*)&lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg___lam__0(lean_object* v_00_u03b7_1_, lean_object* v_00_u03be_2_, lean_object* v_toMul_3_, lean_object* v_toSub_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v_fst_8_; lean_object* v_snd_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_fst_6_ = lean_ctor_get(v_00_u03b7_1_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_00_u03b7_1_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v_00_u03b7_1_);
v_fst_8_ = lean_ctor_get(v_00_u03be_2_, 0);
lean_inc(v_fst_8_);
v_snd_9_ = lean_ctor_get(v_00_u03be_2_, 1);
lean_inc(v_snd_9_);
lean_dec_ref(v_00_u03be_2_);
lean_inc_n(v_i_5_, 3);
v___x_10_ = lean_apply_1(v_snd_7_, v_i_5_);
v___x_11_ = lean_apply_1(v_fst_8_, v_i_5_);
lean_inc(v_toMul_3_);
v___x_12_ = lean_apply_2(v_toMul_3_, v___x_10_, v___x_11_);
v___x_13_ = lean_apply_1(v_snd_9_, v_i_5_);
v___x_14_ = lean_apply_1(v_fst_6_, v_i_5_);
v___x_15_ = lean_apply_2(v_toMul_3_, v___x_13_, v___x_14_);
v___x_16_ = lean_apply_2(v_toSub_4_, v___x_12_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg(lean_object* v_d_17_, lean_object* v_inst_18_, lean_object* v_00_u03be_19_, lean_object* v_00_u03b7_20_){
_start:
{
lean_object* v_toSemiring_21_; lean_object* v_toAddCommMonoid_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_toSub_25_; lean_object* v___x_26_; lean_object* v_toMul_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___x_30_; 
v_toSemiring_21_ = lean_ctor_get(v_inst_18_, 0);
lean_inc_ref(v_toSemiring_21_);
v_toAddCommMonoid_22_ = lean_ctor_get(v_toSemiring_21_, 0);
lean_inc_ref(v_toAddCommMonoid_22_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_18_);
v___x_24_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_23_);
lean_dec_ref(v___x_23_);
v_toSub_25_ = lean_ctor_get(v___x_24_, 2);
lean_inc(v_toSub_25_);
lean_dec_ref(v___x_24_);
v___x_26_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_21_);
v_toMul_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_toMul_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = l_List_finRange(v_d_17_);
v___f_29_ = lean_alloc_closure((void*)(lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg___lam__0), 5, 4);
lean_closure_set(v___f_29_, 0, v_00_u03b7_20_);
lean_closure_set(v___f_29_, 1, v_00_u03be_19_);
lean_closure_set(v___f_29_, 2, v_toMul_27_);
lean_closure_set(v___f_29_, 3, v_toSub_25_);
v___x_30_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_22_, v___x_28_, v___f_29_);
lean_dec_ref(v_toAddCommMonoid_22_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH(lean_object* v_d_31_, lean_object* v_k_32_, lean_object* v_inst_33_, lean_object* v_00_u03be_34_, lean_object* v_00_u03b7_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_ReciprocityTheory_ChartRestriction_G_TB_betaH___redArg(v_d_31_, v_inst_33_, v_00_u03be_34_, v_00_u03b7_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0(lean_object* v_i_37_, lean_object* v___y_38_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0___boxed(lean_object* v_i_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___lam__0(v_i_39_, v___y_40_);
lean_dec_ref(v___y_40_);
lean_dec(v_i_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero(lean_object* v_R_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___f_45_; 
v___f_45_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___closed__0));
return v___f_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero___boxed(lean_object* v_R_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_tree_ReciprocityTheory_ChartRestriction_G_TB_fglZero(v_R_46_, v_inst_47_);
lean_dec_ref(v_inst_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0(lean_object* v_x_49_, lean_object* v_i_50_, lean_object* v___y_51_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0___boxed(lean_object* v_x_52_, lean_object* v_i_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___lam__0(v_x_52_, v_i_53_, v___y_54_);
lean_dec_ref(v___y_54_);
lean_dec(v_i_53_);
lean_dec(v_x_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero(lean_object* v_R_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___f_59_; 
v___f_59_ = ((lean_object*)(lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___closed__0));
return v___f_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero___boxed(lean_object* v_R_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_tree_ReciprocityTheory_ChartRestriction_G_TB_oactZero(v_R_60_, v_inst_61_);
lean_dec_ref(v_inst_61_);
return v_res_62_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
