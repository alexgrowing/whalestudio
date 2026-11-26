// Lean compiler output
// Module: Lib.General.LinearAlgebra.BlockEmbeddings
// Imports: public import Init public meta import Init public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card public import Lib.Weil.DualPair.Defs public import Lib.Weil.Unramified.HeckeGL
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
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_inclMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_inclMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__0(lean_object* v_u_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_u_1_, v___y_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__1(lean_object* v_toOne_4_, lean_object* v_x_5_){
_start:
{
lean_inc(v_toOne_4_);
return v_toOne_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__1___boxed(lean_object* v_toOne_6_, lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_extendGL___redArg___lam__1(v_toOne_6_, v_x_7_);
lean_dec(v_x_7_);
lean_dec(v_toOne_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__3(lean_object* v_inst_9_, lean_object* v_toZero_10_, lean_object* v_toOne_11_, lean_object* v___f_12_, lean_object* v___y_13_, lean_object* v_j_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_GRH_New_inclMatrix___redArg(v_inst_9_, v_toZero_10_, v_toOne_11_, v___f_12_, v___y_13_, v_j_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__2(lean_object* v_g_16_, lean_object* v_j_17_, lean_object* v_inst_18_, lean_object* v_toZero_19_, lean_object* v___f_20_, lean_object* v_toSub_21_, lean_object* v_j_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_inc(v_j_17_);
lean_inc(v_j_22_);
v___x_23_ = lean_apply_2(v_g_16_, v_j_22_, v_j_17_);
v___x_24_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_18_, v_toZero_19_, v___f_20_, v_j_22_, v_j_17_);
v___x_25_ = lean_apply_2(v_toSub_21_, v___x_23_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__4(lean_object* v_g_26_, lean_object* v_inst_27_, lean_object* v_toZero_28_, lean_object* v___f_29_, lean_object* v_toSub_30_, lean_object* v_inst_31_, lean_object* v_toMul_32_, lean_object* v_toAddCommMonoid_33_, lean_object* v___f_34_, lean_object* v_j_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; 
v___f_36_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__2), 7, 6);
lean_closure_set(v___f_36_, 0, v_g_26_);
lean_closure_set(v___f_36_, 1, v_j_35_);
lean_closure_set(v___f_36_, 2, v_inst_27_);
lean_closure_set(v___f_36_, 3, v_toZero_28_);
lean_closure_set(v___f_36_, 4, v___f_29_);
lean_closure_set(v___f_36_, 5, v_toSub_30_);
v___x_37_ = lp_mathlib_dotProduct___redArg(v_inst_31_, v_toMul_32_, v_toAddCommMonoid_33_, v___f_34_, v___f_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__4___boxed(lean_object* v_g_38_, lean_object* v_inst_39_, lean_object* v_toZero_40_, lean_object* v___f_41_, lean_object* v_toSub_42_, lean_object* v_inst_43_, lean_object* v_toMul_44_, lean_object* v_toAddCommMonoid_45_, lean_object* v___f_46_, lean_object* v_j_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_extendGL___redArg___lam__4(v_g_38_, v_inst_39_, v_toZero_40_, v___f_41_, v_toSub_42_, v_inst_43_, v_toMul_44_, v_toAddCommMonoid_45_, v___f_46_, v_j_47_);
lean_dec_ref(v_toAddCommMonoid_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__5(lean_object* v___x_49_, lean_object* v___y_50_, lean_object* v_j_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_mathlib_Matrix_transpose___redArg(v___x_49_, v_j_51_, v___y_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg___lam__6(lean_object* v_inst_53_, lean_object* v_toZero_54_, lean_object* v_toOne_55_, lean_object* v___f_56_, lean_object* v_inst_57_, lean_object* v___f_58_, lean_object* v_toSub_59_, lean_object* v_inst_60_, lean_object* v_toMul_61_, lean_object* v_toAddCommMonoid_62_, lean_object* v___f_63_, lean_object* v_toAdd_64_, lean_object* v_g_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_inc(v___y_66_);
lean_inc(v___f_56_);
lean_inc(v_toOne_55_);
lean_inc_n(v_toZero_54_, 3);
lean_inc_ref_n(v_inst_53_, 2);
v___f_68_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__3), 6, 5);
lean_closure_set(v___f_68_, 0, v_inst_53_);
lean_closure_set(v___f_68_, 1, v_toZero_54_);
lean_closure_set(v___f_68_, 2, v_toOne_55_);
lean_closure_set(v___f_68_, 3, v___f_56_);
lean_closure_set(v___f_68_, 4, v___y_66_);
lean_inc_ref(v_toAddCommMonoid_62_);
lean_inc(v_toMul_61_);
lean_inc(v_inst_60_);
v___f_69_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_69_, 0, v_g_65_);
lean_closure_set(v___f_69_, 1, v_inst_57_);
lean_closure_set(v___f_69_, 2, v_toZero_54_);
lean_closure_set(v___f_69_, 3, v___f_58_);
lean_closure_set(v___f_69_, 4, v_toSub_59_);
lean_closure_set(v___f_69_, 5, v_inst_60_);
lean_closure_set(v___f_69_, 6, v_toMul_61_);
lean_closure_set(v___f_69_, 7, v_toAddCommMonoid_62_);
lean_closure_set(v___f_69_, 8, v___f_68_);
v___x_70_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix), 9, 7);
lean_closure_set(v___x_70_, 0, lean_box(0));
lean_closure_set(v___x_70_, 1, lean_box(0));
lean_closure_set(v___x_70_, 2, v_inst_53_);
lean_closure_set(v___x_70_, 3, lean_box(0));
lean_closure_set(v___x_70_, 4, v_toZero_54_);
lean_closure_set(v___x_70_, 5, v_toOne_55_);
lean_closure_set(v___x_70_, 6, v___f_56_);
lean_inc(v___y_67_);
v___f_71_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__5), 3, 2);
lean_closure_set(v___f_71_, 0, v___x_70_);
lean_closure_set(v___f_71_, 1, v___y_67_);
v___x_72_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_53_, v_toZero_54_, v___f_63_, v___y_66_, v___y_67_);
v___x_73_ = lp_mathlib_dotProduct___redArg(v_inst_60_, v_toMul_61_, v_toAddCommMonoid_62_, v___f_69_, v___f_71_);
lean_dec_ref(v_toAddCommMonoid_62_);
v___x_74_ = lean_apply_2(v_toAdd_64_, v___x_72_, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___redArg(lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_u_79_){
_start:
{
lean_object* v_toSemiring_80_; lean_object* v___x_81_; lean_object* v_toMul_82_; lean_object* v_toAdd_83_; lean_object* v___x_84_; lean_object* v_toZero_85_; lean_object* v___x_86_; lean_object* v_toAddMonoidWithOne_87_; lean_object* v_toOne_88_; lean_object* v_toAddCommMonoid_89_; lean_object* v___x_90_; lean_object* v_toSub_91_; lean_object* v___f_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; 
v_toSemiring_80_ = lean_ctor_get(v_inst_75_, 0);
lean_inc_ref_n(v_toSemiring_80_, 3);
v___x_81_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_80_);
v_toMul_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_toMul_82_);
v_toAdd_83_ = lean_ctor_get(v___x_81_, 1);
lean_inc(v_toAdd_83_);
lean_dec_ref(v___x_81_);
v___x_84_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_80_);
v_toZero_85_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_toZero_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_75_);
v_toAddMonoidWithOne_87_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_toAddMonoidWithOne_87_);
v_toOne_88_ = lean_ctor_get(v_toAddMonoidWithOne_87_, 2);
lean_inc_n(v_toOne_88_, 2);
lean_dec_ref(v_toAddMonoidWithOne_87_);
v_toAddCommMonoid_89_ = lean_ctor_get(v_toSemiring_80_, 0);
lean_inc_ref(v_toAddCommMonoid_89_);
lean_dec_ref(v_toSemiring_80_);
v___x_90_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_86_);
lean_dec_ref(v___x_86_);
v_toSub_91_ = lean_ctor_get(v___x_90_, 2);
lean_inc(v_toSub_91_);
lean_dec_ref(v___x_90_);
v___f_92_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__0), 2, 1);
lean_closure_set(v___f_92_, 0, v_u_79_);
v___f_93_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_93_, 0, v_toOne_88_);
lean_inc_ref(v___f_93_);
v___f_94_ = lean_alloc_closure((void*)(lp_GRH_New_extendGL___redArg___lam__6), 15, 12);
lean_closure_set(v___f_94_, 0, v_inst_76_);
lean_closure_set(v___f_94_, 1, v_toZero_85_);
lean_closure_set(v___f_94_, 2, v_toOne_88_);
lean_closure_set(v___f_94_, 3, v___f_92_);
lean_closure_set(v___f_94_, 4, v_inst_78_);
lean_closure_set(v___f_94_, 5, v___f_93_);
lean_closure_set(v___f_94_, 6, v_toSub_91_);
lean_closure_set(v___f_94_, 7, v_inst_77_);
lean_closure_set(v___f_94_, 8, v_toMul_82_);
lean_closure_set(v___f_94_, 9, v_toAddCommMonoid_89_);
lean_closure_set(v___f_94_, 10, v___f_93_);
lean_closure_set(v___f_94_, 11, v_toAdd_83_);
v___f_95_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_95_, 0, v___f_94_);
return v___f_95_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL(lean_object* v_r_96_, lean_object* v_n_97_, lean_object* v_R_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_u_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_GRH_New_extendGL___redArg(v_inst_99_, v_inst_101_, v_inst_102_, v_inst_103_, v_u_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_extendGL___boxed(lean_object* v_r_106_, lean_object* v_n_107_, lean_object* v_R_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_u_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_GRH_New_extendGL(v_r_106_, v_n_107_, v_R_108_, v_inst_109_, v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_u_114_);
lean_dec(v_inst_110_);
return v_res_115_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Matrix_GeneralLinearGroup_Card(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_DualPair_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Unramified_HeckeGL(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_BlockEmbeddings(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_LinearAlgebra_Matrix_GeneralLinearGroup_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_DualPair_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Unramified_HeckeGL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
