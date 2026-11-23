// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.CoefCol
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions public import Formalism.LocalToGlobal.Columns.StdLatUnimodular public import Formalism.LocalToGlobal.Divisibility.CoefMod
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
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toModule___redArg(lean_object*);
lean_object* lp_mathlib_Pi_Function_module___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_ufGL___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_ufGL___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_ufGL___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_LshKer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_LshKer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0(lean_object* v_toAddCommMonoid_1_, lean_object* v_i_2_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_1_);
return v_toAddCommMonoid_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0(v_toAddCommMonoid_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec_ref(v_toAddCommMonoid_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm___redArg(lean_object* v_inst_6_, lean_object* v_n_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v_toAddCommMonoid_11_; lean_object* v_toCommRing_12_; lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_6_);
v___x_9_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toSemiring_10_);
lean_dec_ref(v___x_9_);
v_toAddCommMonoid_11_ = lean_ctor_get(v_toSemiring_10_, 0);
v_toCommRing_12_ = lean_ctor_get(v_inst_6_, 0);
lean_inc_ref(v_toCommRing_12_);
lean_dec_ref(v_inst_6_);
lean_inc_ref(v_toAddCommMonoid_11_);
v___f_13_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_toGLm___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_13_, 0, v_toAddCommMonoid_11_);
v___x_14_ = lp_mathlib_Semiring_toModule___redArg(v_toSemiring_10_);
v___x_15_ = lp_mathlib_Pi_Function_module___redArg(v___x_14_);
lean_inc(v_n_7_);
v___x_16_ = l_List_finRange(v_n_7_);
v___x_17_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_13_);
v___x_18_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_18_, 0, v_n_7_);
v___x_19_ = lp_mathlib_LinearMap_GeneralLinearGroup_generalLinearEquiv___redArg(v_toSemiring_10_, v___x_17_, v___x_15_);
v___x_20_ = lp_mathlib_Equiv_symm___redArg(v___x_19_);
v___x_21_ = lp_mathlib_Matrix_GeneralLinearGroup_toLin___redArg(v___x_18_, v___x_16_, v_toCommRing_12_);
v___x_22_ = lp_mathlib_Equiv_symm___redArg(v___x_21_);
v___x_23_ = lp_mathlib_Equiv_trans___redArg(v___x_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toGLm(lean_object* v_E_24_, lean_object* v_inst_25_, lean_object* v_n_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_tree_Formalism_L2_Col_toGLm___redArg(v_inst_25_, v_n_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL___redArg(lean_object* v_inst_29_, lean_object* v_n_30_){
_start:
{
lean_object* v___x_31_; lean_object* v_toFun_32_; lean_object* v___f_33_; lean_object* v___f_34_; 
v___x_31_ = lp_tree_Formalism_L2_Col_toGLm___redArg(v_inst_29_, v_n_30_);
v_toFun_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_toFun_32_);
lean_dec_ref(v___x_31_);
v___f_33_ = ((lean_object*)(lp_tree_Formalism_L2_Col_ufGL___redArg___closed__0));
v___f_34_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_34_, 0, v___f_33_);
lean_closure_set(v___f_34_, 1, v_toFun_32_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL(lean_object* v_E_35_, lean_object* v_inst_36_, lean_object* v_n_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_tree_Formalism_L2_Col_ufGL___redArg(v_inst_36_, v_n_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_ufGL___boxed(lean_object* v_E_40_, lean_object* v_inst_41_, lean_object* v_n_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_L2_Col_ufGL(v_E_40_, v_inst_41_, v_n_42_, v_inst_43_);
lean_dec(v_inst_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__0(lean_object* v_e_45_, lean_object* v_Nab_46_, lean_object* v_d_x27_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_apply_1(v_e_45_, v_d_x27_47_);
v___x_49_ = lean_apply_1(v_Nab_46_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__1(lean_object* v_e_50_, lean_object* v_Del_51_, lean_object* v_d_x27_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_apply_1(v_e_50_, v_d_x27_52_);
v___x_54_ = lean_apply_1(v_Del_51_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___redArg(lean_object* v_C_55_, lean_object* v_e_56_){
_start:
{
lean_object* v_lam_57_; lean_object* v_rho_58_; lean_object* v_pair_59_; lean_object* v_Nab_60_; lean_object* v_Del_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_70_; 
v_lam_57_ = lean_ctor_get(v_C_55_, 0);
v_rho_58_ = lean_ctor_get(v_C_55_, 1);
v_pair_59_ = lean_ctor_get(v_C_55_, 2);
v_Nab_60_ = lean_ctor_get(v_C_55_, 3);
v_Del_61_ = lean_ctor_get(v_C_55_, 4);
v_isSharedCheck_70_ = !lean_is_exclusive(v_C_55_);
if (v_isSharedCheck_70_ == 0)
{
v___x_63_ = v_C_55_;
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_Del_61_);
lean_inc(v_Nab_60_);
lean_inc(v_pair_59_);
lean_inc(v_rho_58_);
lean_inc(v_lam_57_);
lean_dec(v_C_55_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___f_65_; lean_object* v___f_66_; lean_object* v___x_68_; 
lean_inc(v_e_56_);
v___f_65_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__0), 3, 2);
lean_closure_set(v___f_65_, 0, v_e_56_);
lean_closure_set(v___f_65_, 1, v_Nab_60_);
v___f_66_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_CoefPk_pull___redArg___lam__1), 3, 2);
lean_closure_set(v___f_66_, 0, v_e_56_);
lean_closure_set(v___f_66_, 1, v_Del_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 4, v___f_66_);
lean_ctor_set(v___x_63_, 3, v___f_65_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_lam_57_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_rho_58_);
lean_ctor_set(v_reuseFailAlloc_69_, 2, v_pair_59_);
lean_ctor_set(v_reuseFailAlloc_69_, 3, v___f_65_);
lean_ctor_set(v_reuseFailAlloc_69_, 4, v___f_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull(lean_object* v_X_71_, lean_object* v_n_72_, lean_object* v_D_73_, lean_object* v_C_74_, lean_object* v_D_x27_75_, lean_object* v_e_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_tree_Formalism_L2_Col_CoefPk_pull___redArg(v_C_74_, v_e_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_CoefPk_pull___boxed(lean_object* v_X_78_, lean_object* v_n_79_, lean_object* v_D_80_, lean_object* v_C_81_, lean_object* v_D_x27_82_, lean_object* v_e_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_tree_Formalism_L2_Col_CoefPk_pull(v_X_78_, v_n_79_, v_D_80_, v_C_81_, v_D_x27_82_, v_e_83_);
lean_dec(v_n_79_);
lean_dec_ref(v_X_78_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_LshKer(lean_object* v_E_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_n_88_, lean_object* v_ST_89_, lean_object* v_SG_90_, lean_object* v_d_91_, lean_object* v_P_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_box(0);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Deco_LshKer___boxed(lean_object* v_E_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_n_97_, lean_object* v_ST_98_, lean_object* v_SG_99_, lean_object* v_d_100_, lean_object* v_P_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = lp_tree_Formalism_L2_Col_Deco_LshKer(v_E_94_, v_inst_95_, v_inst_96_, v_n_97_, v_ST_98_, v_SG_99_, v_d_100_, v_P_101_);
lean_dec_ref(v_d_100_);
lean_dec(v_SG_99_);
lean_dec(v_ST_98_);
lean_dec(v_n_97_);
lean_dec(v_inst_96_);
lean_dec_ref(v_inst_95_);
return v_res_102_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefMod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefCol(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_AbelianHostFieldConditions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_StdLatUnimodular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_CoefMod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
