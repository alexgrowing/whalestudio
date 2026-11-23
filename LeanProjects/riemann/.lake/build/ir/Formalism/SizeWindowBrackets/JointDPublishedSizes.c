// Lean compiler output
// Module: Formalism.SizeWindowBrackets.JointDPublishedSizes
// Imports: public import Init public meta import Init public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqEmpty___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_linePt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0;
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_stdLat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_stdLat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_linePt(lean_object* v_p_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v_fst_7_; 
v___x_4_ = lp_mathlib_ZMod_commRing(v_p_1_);
v_toSemiring_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_5_);
v_fst_7_ = lean_ctor_get(v_x_2_, 0);
if (lean_obj_tag(v_fst_7_) == 0)
{
lean_object* v_snd_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_15_; 
lean_dec_ref(v___x_6_);
v_snd_8_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_15_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v_x_2_, 0);
lean_dec(v_unused_16_);
v___x_10_ = v_x_2_;
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_snd_8_);
lean_dec(v_x_2_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_15_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_13_; 
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 1, v_x_3_);
lean_ctor_set(v___x_10_, 0, v_snd_8_);
v___x_13_ = v___x_10_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v_snd_8_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v_x_3_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
else
{
lean_object* v_toMul_17_; lean_object* v_toAdd_18_; lean_object* v_snd_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
lean_inc_ref(v_fst_7_);
v_toMul_17_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_toMul_17_);
v_toAdd_18_ = lean_ctor_get(v___x_6_, 1);
lean_inc(v_toAdd_18_);
lean_dec_ref(v___x_6_);
v_snd_19_ = lean_ctor_get(v_x_2_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; 
v_unused_30_ = lean_ctor_get(v_x_2_, 0);
lean_dec(v_unused_30_);
v___x_21_ = v_x_2_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snd_19_);
lean_dec(v_x_2_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v_val_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
v_val_23_ = lean_ctor_get(v_fst_7_, 0);
lean_inc(v_val_23_);
lean_dec_ref_known(v_fst_7_, 1);
lean_inc(v_x_3_);
v___x_24_ = lean_apply_2(v_toMul_17_, v_val_23_, v_x_3_);
v___x_25_ = lean_apply_2(v_toAdd_18_, v___x_24_, v_snd_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_25_);
lean_ctor_set(v___x_21_, 0, v_x_3_);
v___x_27_ = v___x_21_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_x_3_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT uint8_t lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0(lean_object* v_p_31_, lean_object* v_a_32_, lean_object* v_b_33_){
_start:
{
lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_34_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_34_, 0, v_p_31_);
lean_inc_ref(v___x_34_);
v___x_35_ = l_instDecidableEqProd___redArg(v___x_34_, v___x_34_, v_a_32_, v_b_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0___boxed(lean_object* v_p_36_, lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0(v_p_36_, v_a_37_, v_b_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
v___x_42_ = lp_mathlib_Complex_ofReal(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
v___x_44_ = lp_mathlib_Complex_ofReal(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1(lean_object* v_p_45_, lean_object* v_i_46_, lean_object* v___f_47_, lean_object* v_a_48_, lean_object* v_t_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_50_ = lean_alloc_closure((void*)(l_instDecidableEqEmpty___boxed), 2, 0);
v___x_51_ = lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_linePt(v_p_45_, v_i_46_, v_t_49_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = l_instDecidableEqSum_decEq___redArg(v___f_47_, v___x_50_, v_a_48_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0);
return v___x_54_;
}
else
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1);
return v___x_55_;
}
}
}
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat(lean_object* v_p_57_, lean_object* v_i_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; lean_object* v_toFun_62_; lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v___x_61_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___closed__0);
v_toFun_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_p_57_);
v___f_63_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__0___boxed), 3, 1);
lean_closure_set(v___f_63_, 0, v_p_57_);
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1), 5, 3);
lean_closure_set(v___f_64_, 0, v_p_57_);
lean_closure_set(v___f_64_, 1, v_i_58_);
lean_closure_set(v___f_64_, 2, v___f_63_);
lean_inc(v_toFun_62_);
v___x_65_ = lean_apply_3(v_toFun_62_, v___f_64_, v_a_59_, v_a_60_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_stdLat(lean_object* v_K_66_, lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_inst_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_stdLat___boxed(lean_object* v_K_72_, lean_object* v_n_73_, lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_stdLat(v_K_72_, v_n_73_, v_inst_74_, v_inst_75_, v_inst_76_);
lean_dec(v_inst_76_);
lean_dec_ref(v_inst_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___lam__0(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_a_80_, lean_object* v_k_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v_k_81_);
v___x_83_ = l_instDecidableEqSum_decEq___redArg(v_inst_78_, v_inst_79_, v_a_80_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__0);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_lineMat___lam__1___closed__1);
return v___x_85_;
}
}
}
static lean_object* _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg(lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_91_; lean_object* v_toFun_92_; lean_object* v___f_93_; lean_object* v___x_94_; 
v___x_91_ = lean_obj_once(&lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0, &lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0_once, _init_lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___closed__0);
v_toFun_92_ = lean_ctor_get(v___x_91_, 0);
v___f_93_ = lean_alloc_closure((void*)(lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg___lam__0), 4, 2);
lean_closure_set(v___f_93_, 0, v_inst_87_);
lean_closure_set(v___f_93_, 1, v_inst_88_);
lean_inc(v_toFun_92_);
v___x_94_ = lean_apply_3(v_toFun_92_, v___f_93_, v_a_89_, v_a_90_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat(lean_object* v_00_u03ba_95_, lean_object* v_00_u03ba_u2081_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lp_tree_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclMat___redArg(v_inst_97_, v_inst_98_, v_a_99_, v_a_100_);
return v___x_101_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SizeWindowBrackets_JointDPublishedSizes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
