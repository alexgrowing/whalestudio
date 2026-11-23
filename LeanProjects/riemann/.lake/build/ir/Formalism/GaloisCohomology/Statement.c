// Lean compiler output
// Module: Formalism.GaloisCohomology.Statement
// Imports: public import Init public meta import Init public import ReciprocityTheory.Hypotheses.GalCoh
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
lean_object* lp_mathlib_TopologicalSpace_instCompleteLattice(lean_object*);
lean_object* lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0;
static lean_once_cell_t lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_unrAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_unrAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_SelAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_SelAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_TopologicalSpace_instCompleteLattice(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0, &lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0_once, _init_lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__0);
v___x_3_ = lp_mathlib_CompleteLattice_toCompletePartialOrder___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ(lean_object* v_l_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v___x_6_; lean_object* v_toOrderBot_7_; 
v___x_6_ = lean_obj_once(&lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1, &lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1_once, _init_lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___closed__1);
v_toOrderBot_7_ = lean_ctor_get(v___x_6_, 2);
lean_inc(v_toOrderBot_7_);
return v_toOrderBot_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ___boxed(lean_object* v_l_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_GaloisCohomology_instTopologicalSpaceQZ(v_l_8_, v_inst_9_);
lean_dec(v_l_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___redArg___lam__0(lean_object* v_00_u03c8_11_, lean_object* v_inst_12_, lean_object* v_g_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_15_; lean_object* v_val_16_; lean_object* v___x_17_; 
v___x_15_ = lean_apply_1(v_00_u03c8_11_, v_g_13_);
v_val_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_val_16_);
lean_dec_ref(v___x_15_);
v___x_17_ = lean_apply_2(v_inst_12_, v_val_16_, v___y_14_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___redArg(lean_object* v_inst_18_, lean_object* v_00_u03c8_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = lean_alloc_closure((void*)(lp_tree_Formalism_GaloisCohomology_scalRep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_20_, 0, v_00_u03c8_19_);
lean_closure_set(v___f_20_, 1, v_inst_18_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep(lean_object* v_R_21_, lean_object* v_inst_22_, lean_object* v_00_u0393_23_, lean_object* v_inst_24_, lean_object* v_M_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_00_u03c8_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_GaloisCohomology_scalRep___redArg___lam__0), 4, 2);
lean_closure_set(v___f_29_, 0, v_00_u03c8_28_);
lean_closure_set(v___f_29_, 1, v_inst_27_);
return v___f_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_scalRep___boxed(lean_object* v_R_30_, lean_object* v_inst_31_, lean_object* v_00_u0393_32_, lean_object* v_inst_33_, lean_object* v_M_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_00_u03c8_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_tree_Formalism_GaloisCohomology_scalRep(v_R_30_, v_inst_31_, v_00_u0393_32_, v_inst_33_, v_M_34_, v_inst_35_, v_inst_36_, v_00_u03c8_37_);
lean_dec_ref(v_inst_35_);
lean_dec_ref(v_inst_33_);
lean_dec_ref(v_inst_31_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_unrAt(lean_object* v_F_39_, lean_object* v_00_u03a9_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_R_45_, lean_object* v_inst_46_, lean_object* v_M_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_rho_53_, lean_object* v_A_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(0);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_unrAt___boxed(lean_object* v_F_56_, lean_object* v_00_u03a9_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_R_62_, lean_object* v_inst_63_, lean_object* v_M_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_rho_70_, lean_object* v_A_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_Formalism_GaloisCohomology_unrAt(v_F_56_, v_00_u03a9_57_, v_inst_58_, v_inst_59_, v_inst_60_, v_inst_61_, v_R_62_, v_inst_63_, v_M_64_, v_inst_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_rho_70_, v_A_71_);
lean_dec(v_rho_70_);
lean_dec(v_inst_66_);
lean_dec_ref(v_inst_65_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_58_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_SelAll(lean_object* v_F_73_, lean_object* v_00_u03a9_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_R_78_, lean_object* v_inst_79_, lean_object* v_M_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_rho_86_, lean_object* v_A_87_, lean_object* v_L_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_GaloisCohomology_SelAll___boxed(lean_object* v_F_90_, lean_object* v_00_u03a9_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_R_95_, lean_object* v_inst_96_, lean_object* v_M_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_rho_103_, lean_object* v_A_104_, lean_object* v_L_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_Formalism_GaloisCohomology_SelAll(v_F_90_, v_00_u03a9_91_, v_inst_92_, v_inst_93_, v_inst_94_, v_R_95_, v_inst_96_, v_M_97_, v_inst_98_, v_inst_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_rho_103_, v_A_104_, v_L_105_);
lean_dec_ref(v_L_105_);
lean_dec_ref(v_A_104_);
lean_dec(v_rho_103_);
lean_dec(v_inst_99_);
lean_dec_ref(v_inst_98_);
lean_dec_ref(v_inst_96_);
lean_dec_ref(v_inst_94_);
lean_dec_ref(v_inst_93_);
lean_dec_ref(v_inst_92_);
return v_res_106_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_Hypotheses_GalCoh(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_GaloisCohomology_Statement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_Hypotheses_GalCoh(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
