// Lean compiler output
// Module: Lib.General.Algebra.CohomologyBaseChange
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.BijectiveComparisons public import Lib.PadicComparison.Descent.TestCategory
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
lean_object* lp_mathlib_CommAlgCat_instCategory___redArg();
lean_object* lp_mathlib_CategoryTheory_Functor_category___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_whiskeringRight___redArg();
lean_object* lp_GRH_New_Variety_algBaseChange___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_restrictAlg___redArg(lean_object*);
lean_object* lp_mathlib_CommAlgCat_instConcreteCategoryAlgHomCarrier___redArg();
lean_object* lp_mathlib_CategoryTheory_ConcreteCategory_homEquiv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AlgHom_liftEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Adjunction_mkOfHomEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Adjunction_whiskerRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Adjunction_homEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v___x_4_, lean_object* v_toSemiring_5_, lean_object* v_toSemiring_6_, lean_object* v_inst_7_, lean_object* v_A_8_, lean_object* v_B_9_){
_start:
{
lean_object* v_commRing_10_; lean_object* v_commRing_11_; lean_object* v_algebra_12_; lean_object* v_toSemiring_13_; lean_object* v_algebra_14_; lean_object* v_toSemiring_15_; lean_object* v_obj_16_; lean_object* v_obj_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v_algebra_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_commRing_10_ = lean_ctor_get(v_A_8_, 0);
v_commRing_11_ = lean_ctor_get(v_B_9_, 0);
v_algebra_12_ = lean_ctor_get(v_A_8_, 1);
lean_inc_ref(v_algebra_12_);
v_toSemiring_13_ = lean_ctor_get(v_commRing_10_, 0);
lean_inc_ref(v_toSemiring_13_);
v_algebra_14_ = lean_ctor_get(v_B_9_, 1);
lean_inc_ref(v_algebra_14_);
v_toSemiring_15_ = lean_ctor_get(v_commRing_11_, 0);
lean_inc_ref(v_toSemiring_15_);
v_obj_16_ = lean_ctor_get(v___x_1_, 0);
lean_inc(v_obj_16_);
lean_dec_ref(v___x_1_);
v_obj_17_ = lean_ctor_get(v___x_2_, 0);
lean_inc(v_obj_17_);
lean_dec_ref(v___x_2_);
lean_inc_ref(v_A_8_);
v___x_18_ = lean_apply_1(v_obj_16_, v_A_8_);
lean_inc_ref(v_B_9_);
v___x_19_ = lp_mathlib_CategoryTheory_ConcreteCategory_homEquiv___redArg(v___x_3_, v___x_18_, v_B_9_);
v___x_20_ = lean_apply_1(v_obj_17_, v_B_9_);
v_algebra_21_ = lean_ctor_get(v___x_20_, 1);
lean_inc_ref(v_algebra_21_);
v___x_22_ = lp_mathlib_CategoryTheory_ConcreteCategory_homEquiv___redArg(v___x_4_, v_A_8_, v___x_20_);
v___x_23_ = lp_mathlib_AlgHom_liftEquiv___redArg(v_toSemiring_5_, v_toSemiring_6_, v_toSemiring_13_, v_toSemiring_15_, v_algebra_12_, v_algebra_14_, v_inst_7_, v_algebra_21_);
v___x_24_ = lp_mathlib_Equiv_trans___redArg(v___x_22_, v___x_23_);
v___x_25_ = lp_mathlib_Equiv_symm___redArg(v___x_24_);
v___x_26_ = lp_mathlib_Equiv_trans___redArg(v___x_19_, v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_mathlib_CommAlgCat_instCategory___redArg();
return v___x_27_;
}
}
static lean_object* _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_mathlib_CommAlgCat_instConcreteCategoryAlgHomCarrier___redArg();
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj___redArg(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_toSemiring_34_; lean_object* v_toSemiring_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v___x_32_ = lean_obj_once(&lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0, &lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0_once, _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0);
v___x_33_ = lean_obj_once(&lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1, &lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1_once, _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__1);
v_toSemiring_34_ = lean_ctor_get(v_inst_29_, 0);
lean_inc_ref(v_toSemiring_34_);
v_toSemiring_35_ = lean_ctor_get(v_inst_30_, 0);
lean_inc_ref(v_toSemiring_35_);
lean_inc_ref_n(v_inst_31_, 2);
v___x_36_ = lp_GRH_New_Variety_algBaseChange___redArg(v_inst_29_, v_inst_30_, v_inst_31_);
v___x_37_ = lp_GRH_New_Variety_restrictAlg___redArg(v_inst_31_);
lean_inc_ref(v___x_37_);
lean_inc_ref(v___x_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_algBaseChangeAdj___redArg___lam__0), 9, 7);
lean_closure_set(v___f_38_, 0, v___x_36_);
lean_closure_set(v___f_38_, 1, v___x_37_);
lean_closure_set(v___f_38_, 2, v___x_33_);
lean_closure_set(v___f_38_, 3, v___x_33_);
lean_closure_set(v___f_38_, 4, v_toSemiring_34_);
lean_closure_set(v___f_38_, 5, v_toSemiring_35_);
lean_closure_set(v___f_38_, 6, v_inst_31_);
v___x_39_ = lp_mathlib_CategoryTheory_Adjunction_mkOfHomEquiv___redArg(v___x_32_, v___x_32_, v___x_36_, v___x_37_, v___f_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_algBaseChangeAdj(lean_object* v_k_40_, lean_object* v_S_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_GRH_New_Variety_algBaseChangeAdj___redArg(v_inst_42_, v_inst_43_, v_inst_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0, &lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0_once, _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0);
v___x_47_ = lp_mathlib_CategoryTheory_Functor_category___redArg(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_mathlib_CategoryTheory_Functor_whiskeringRight___redArg();
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose___redArg(lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_X_52_, lean_object* v_Y_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_obj_57_; lean_object* v_obj_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_54_ = lean_obj_once(&lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0, &lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0_once, _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0);
v___x_55_ = lean_obj_once(&lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0, &lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0_once, _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0);
v___x_56_ = lean_obj_once(&lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1, &lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1_once, _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1);
v_obj_57_ = lean_ctor_get(v___x_56_, 0);
v_obj_58_ = lean_ctor_get(v___x_56_, 0);
lean_inc_ref_n(v_inst_51_, 2);
lean_inc_ref(v_inst_50_);
lean_inc_ref(v_inst_49_);
v___x_59_ = lp_GRH_New_Variety_algBaseChange___redArg(v_inst_49_, v_inst_50_, v_inst_51_);
lean_inc(v_obj_57_);
lean_inc_ref(v___x_59_);
v___x_60_ = lean_apply_1(v_obj_57_, v___x_59_);
v___x_61_ = lp_GRH_New_Variety_restrictAlg___redArg(v_inst_51_);
lean_inc(v_obj_58_);
lean_inc_ref(v___x_61_);
v___x_62_ = lean_apply_1(v_obj_58_, v___x_61_);
v___x_63_ = lp_GRH_New_Variety_algBaseChangeAdj___redArg(v_inst_49_, v_inst_50_, v_inst_51_);
v___x_64_ = lp_mathlib_CategoryTheory_Adjunction_whiskerRight___redArg(v___x_54_, v___x_54_, v___x_59_, v___x_61_, v___x_63_);
v___x_65_ = lp_mathlib_CategoryTheory_Adjunction_homEquiv___redArg(v___x_55_, v___x_55_, v___x_60_, v___x_62_, v___x_64_, v_X_52_, v_Y_53_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose(lean_object* v_C_66_, lean_object* v_k_67_, lean_object* v_S_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_X_73_, lean_object* v_Y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_obj_78_; lean_object* v_obj_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_75_ = lean_obj_once(&lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0, &lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0_once, _init_lp_GRH_New_Variety_algBaseChangeAdj___redArg___closed__0);
v___x_76_ = lean_obj_once(&lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0, &lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0_once, _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__0);
v___x_77_ = lean_obj_once(&lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1, &lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1_once, _init_lp_GRH_New_Variety_baseChangeTranspose___redArg___closed__1);
v_obj_78_ = lean_ctor_get(v___x_77_, 0);
v_obj_79_ = lean_ctor_get(v___x_77_, 0);
lean_inc_ref_n(v_inst_72_, 2);
lean_inc_ref(v_inst_71_);
lean_inc_ref(v_inst_70_);
v___x_80_ = lp_GRH_New_Variety_algBaseChange___redArg(v_inst_70_, v_inst_71_, v_inst_72_);
lean_inc(v_obj_78_);
lean_inc_ref(v___x_80_);
v___x_81_ = lean_apply_1(v_obj_78_, v___x_80_);
v___x_82_ = lp_GRH_New_Variety_restrictAlg___redArg(v_inst_72_);
lean_inc(v_obj_79_);
lean_inc_ref(v___x_82_);
v___x_83_ = lean_apply_1(v_obj_79_, v___x_82_);
v___x_84_ = lp_GRH_New_Variety_algBaseChangeAdj___redArg(v_inst_70_, v_inst_71_, v_inst_72_);
v___x_85_ = lp_mathlib_CategoryTheory_Adjunction_whiskerRight___redArg(v___x_75_, v___x_75_, v___x_80_, v___x_82_, v___x_84_);
v___x_86_ = lp_mathlib_CategoryTheory_Adjunction_homEquiv___redArg(v___x_76_, v___x_76_, v___x_81_, v___x_83_, v___x_85_, v_X_73_, v_Y_74_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_baseChangeTranspose___boxed(lean_object* v_C_87_, lean_object* v_k_88_, lean_object* v_S_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_X_94_, lean_object* v_Y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_GRH_New_Variety_baseChangeTranspose(v_C_87_, v_k_88_, v_S_89_, v_inst_90_, v_inst_91_, v_inst_92_, v_inst_93_, v_X_94_, v_Y_95_);
lean_dec_ref(v_inst_90_);
return v_res_96_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_Descent_TestCategory(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_Algebra_CohomologyBaseChange(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_BijectiveComparisons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_Descent_TestCategory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
