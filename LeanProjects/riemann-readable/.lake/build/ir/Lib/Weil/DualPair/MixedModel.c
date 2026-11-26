// Lean compiler output
// Module: Lib.Weil.DualPair.MixedModel
// Imports: public import Init public meta import Init public import Lib.Weil.DualPair.WeilAction
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_kroneckerMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__0(lean_object* v_toMul_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_toMul_1_, v_x1_2_, v_x2_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1(lean_object* v_toOne_5_, lean_object* v_x_6_){
_start:
{
lean_inc(v_toOne_5_);
return v_toOne_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1___boxed(lean_object* v_toOne_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1(v_toOne_7_, v_x_8_);
lean_dec(v_x_8_);
lean_dec(v_toOne_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_D_12_, lean_object* v_T_13_){
_start:
{
lean_object* v___x_14_; lean_object* v_toCommSemiring_15_; lean_object* v___x_16_; lean_object* v_toMul_17_; lean_object* v___x_18_; lean_object* v_toZero_19_; lean_object* v___x_20_; lean_object* v_toRing_21_; lean_object* v___x_22_; lean_object* v_toAddMonoidWithOne_23_; lean_object* v_toOne_24_; lean_object* v_k_25_; lean_object* v_l_26_; lean_object* v_i_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_42_; 
v___x_14_ = lp_mathlib_Field_toSemifield___redArg(v_inst_10_);
v_toCommSemiring_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc_ref_n(v_toCommSemiring_15_, 2);
lean_dec_ref(v___x_14_);
v___x_16_ = lp_mathlib_instDistribOfSemiring___redArg(v_toCommSemiring_15_);
v_toMul_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc(v_toMul_17_);
lean_dec_ref(v___x_16_);
v___x_18_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toCommSemiring_15_);
v_toZero_19_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_toZero_19_);
lean_dec_ref(v___x_18_);
v___x_20_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_10_);
v_toRing_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc_ref(v_toRing_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_21_);
v_toAddMonoidWithOne_23_ = lean_ctor_get(v___x_22_, 1);
lean_inc_ref(v_toAddMonoidWithOne_23_);
lean_dec_ref(v___x_22_);
v_toOne_24_ = lean_ctor_get(v_toAddMonoidWithOne_23_, 2);
lean_inc(v_toOne_24_);
lean_dec_ref(v_toAddMonoidWithOne_23_);
v_k_25_ = lean_ctor_get(v_D_12_, 0);
v_l_26_ = lean_ctor_get(v_D_12_, 1);
v_i_27_ = lean_ctor_get(v_D_12_, 2);
v_isSharedCheck_42_ = !lean_is_exclusive(v_D_12_);
if (v_isSharedCheck_42_ == 0)
{
v___x_29_ = v_D_12_;
v_isShared_30_ = v_isSharedCheck_42_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_i_27_);
lean_inc(v_l_26_);
lean_inc(v_k_25_);
lean_dec(v_D_12_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_42_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v_J_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v_J_31_ = lean_ctor_get(v_T_13_, 0);
lean_inc(v_J_31_);
lean_dec_ref(v_T_13_);
v___f_32_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_homTarget___redArg___lam__0), 3, 1);
lean_closure_set(v___f_32_, 0, v_toMul_17_);
v___f_33_ = lean_alloc_closure((void*)(lp_GRH_New_Space_Splitting_homTarget___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_33_, 0, v_toOne_24_);
v___x_34_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_34_, 0, lean_box(0));
lean_closure_set(v___x_34_, 1, lean_box(0));
lean_closure_set(v___x_34_, 2, lean_box(0));
lean_closure_set(v___x_34_, 3, v_J_31_);
lean_inc_ref_n(v___f_32_, 2);
v___x_35_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_kroneckerMap), 12, 10);
lean_closure_set(v___x_35_, 0, lean_box(0));
lean_closure_set(v___x_35_, 1, lean_box(0));
lean_closure_set(v___x_35_, 2, lean_box(0));
lean_closure_set(v___x_35_, 3, lean_box(0));
lean_closure_set(v___x_35_, 4, lean_box(0));
lean_closure_set(v___x_35_, 5, lean_box(0));
lean_closure_set(v___x_35_, 6, lean_box(0));
lean_closure_set(v___x_35_, 7, v___f_32_);
lean_closure_set(v___x_35_, 8, v_k_25_);
lean_closure_set(v___x_35_, 9, v___x_34_);
v___x_36_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_36_, 0, lean_box(0));
lean_closure_set(v___x_36_, 1, lean_box(0));
lean_closure_set(v___x_36_, 2, v_inst_11_);
lean_closure_set(v___x_36_, 3, v_toZero_19_);
lean_closure_set(v___x_36_, 4, v___f_33_);
lean_inc_ref(v___x_36_);
v___x_37_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_kroneckerMap), 12, 10);
lean_closure_set(v___x_37_, 0, lean_box(0));
lean_closure_set(v___x_37_, 1, lean_box(0));
lean_closure_set(v___x_37_, 2, lean_box(0));
lean_closure_set(v___x_37_, 3, lean_box(0));
lean_closure_set(v___x_37_, 4, lean_box(0));
lean_closure_set(v___x_37_, 5, lean_box(0));
lean_closure_set(v___x_37_, 6, lean_box(0));
lean_closure_set(v___x_37_, 7, v___f_32_);
lean_closure_set(v___x_37_, 8, v_l_26_);
lean_closure_set(v___x_37_, 9, v___x_36_);
v___x_38_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_kroneckerMap), 12, 10);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, lean_box(0));
lean_closure_set(v___x_38_, 2, lean_box(0));
lean_closure_set(v___x_38_, 3, lean_box(0));
lean_closure_set(v___x_38_, 4, lean_box(0));
lean_closure_set(v___x_38_, 5, lean_box(0));
lean_closure_set(v___x_38_, 6, lean_box(0));
lean_closure_set(v___x_38_, 7, v___f_32_);
lean_closure_set(v___x_38_, 8, v_i_27_);
lean_closure_set(v___x_38_, 9, v___x_36_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___x_38_);
lean_ctor_set(v___x_29_, 1, v___x_37_);
lean_ctor_set(v___x_29_, 0, v___x_35_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget(lean_object* v_E_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_n_46_, lean_object* v_n_x27_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_s_52_, lean_object* v_s_x27_53_, lean_object* v_n_u2080_54_, lean_object* v_p_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_s_u2080_60_, lean_object* v_V_61_, lean_object* v_V_u2080_62_, lean_object* v_D_63_, lean_object* v_T_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_GRH_New_Space_Splitting_homTarget___redArg(v_inst_44_, v_inst_51_, v_D_63_, v_T_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Space_Splitting_homTarget___boxed(lean_object** _args){
lean_object* v_E_66_ = _args[0];
lean_object* v_inst_67_ = _args[1];
lean_object* v_inst_68_ = _args[2];
lean_object* v_n_69_ = _args[3];
lean_object* v_n_x27_70_ = _args[4];
lean_object* v_inst_71_ = _args[5];
lean_object* v_inst_72_ = _args[6];
lean_object* v_inst_73_ = _args[7];
lean_object* v_inst_74_ = _args[8];
lean_object* v_s_75_ = _args[9];
lean_object* v_s_x27_76_ = _args[10];
lean_object* v_n_u2080_77_ = _args[11];
lean_object* v_p_78_ = _args[12];
lean_object* v_inst_79_ = _args[13];
lean_object* v_inst_80_ = _args[14];
lean_object* v_inst_81_ = _args[15];
lean_object* v_inst_82_ = _args[16];
lean_object* v_s_u2080_83_ = _args[17];
lean_object* v_V_84_ = _args[18];
lean_object* v_V_u2080_85_ = _args[19];
lean_object* v_D_86_ = _args[20];
lean_object* v_T_87_ = _args[21];
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_GRH_New_Space_Splitting_homTarget(v_E_66_, v_inst_67_, v_inst_68_, v_n_69_, v_n_x27_70_, v_inst_71_, v_inst_72_, v_inst_73_, v_inst_74_, v_s_75_, v_s_x27_76_, v_n_u2080_77_, v_p_78_, v_inst_79_, v_inst_80_, v_inst_81_, v_inst_82_, v_s_u2080_83_, v_V_84_, v_V_u2080_85_, v_D_86_, v_T_87_);
lean_dec_ref(v_V_u2080_85_);
lean_dec_ref(v_V_84_);
lean_dec_ref(v_s_u2080_83_);
lean_dec_ref(v_inst_82_);
lean_dec(v_inst_81_);
lean_dec_ref(v_inst_80_);
lean_dec(v_inst_79_);
lean_dec_ref(v_s_x27_76_);
lean_dec_ref(v_s_75_);
lean_dec(v_inst_73_);
lean_dec_ref(v_inst_72_);
lean_dec(v_inst_71_);
lean_dec_ref(v_inst_68_);
return v_res_88_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_WeilAction(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_DualPair_MixedModel(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_DualPair_WeilAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
