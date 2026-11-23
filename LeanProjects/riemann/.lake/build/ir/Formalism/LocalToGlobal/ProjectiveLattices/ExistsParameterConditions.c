// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Pj_levelOfPs___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Rows_Data_phiO___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelG(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_toOF___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_toOF(lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_nat_mod(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_mod(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelG___redArg(lean_object* v_D_7_){
_start:
{
lean_object* v_host_8_; lean_object* v_g_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_host_8_ = lean_ctor_get(v_D_7_, 1);
v_g_9_ = lean_ctor_get(v_host_8_, 6);
v___x_10_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0, &lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0_once, _init_lp_tree_Formalism_L2_Pj_levelG___redArg___closed__0);
lean_inc_ref_n(v_g_9_, 2);
v___x_11_ = lean_apply_1(v_g_9_, v___x_10_);
v___x_12_ = lean_obj_once(&lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1, &lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1_once, _init_lp_tree_Formalism_L2_Pj_levelG___redArg___closed__1);
v___x_13_ = lean_apply_1(v_g_9_, v___x_12_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_11_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lp_tree_Formalism_L2_Pj_levelOfPs___redArg(v_D_7_, v___x_16_);
lean_dec_ref(v_D_7_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_levelG(lean_object* v_D_18_, lean_object* v_hU_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_tree_Formalism_L2_Pj_levelG___redArg(v_D_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_toOF___lam__0(lean_object* v_what_u2082_21_, lean_object* v_y_22_){
_start:
{
lean_object* v___x_59__overap_23_; lean_object* v___x_24_; 
v___x_59__overap_23_ = lp_tree_Formalism_BasicNotions_Rows_Data_phiO___redArg(v_what_u2082_21_);
v___x_24_ = lean_apply_1(v___x_59__overap_23_, v_y_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_toOF(lean_object* v_D_25_){
_start:
{
lean_object* v_what_u2082_26_; lean_object* v___f_27_; 
v_what_u2082_26_ = lean_ctor_get(v_D_25_, 4);
lean_inc_ref(v_what_u2082_26_);
lean_dec_ref(v_D_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Pj_toOF___lam__0), 2, 1);
lean_closure_set(v___f_27_, 0, v_what_u2082_26_);
return v___f_27_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PartitionExtendByZeroAntitone(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HalfOneAddSqrtNegIsIntegral(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible(uint8_t builtin);
lean_object* initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ExistsParameterConditions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_PartitionExtendByZeroAntitone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_HalfOneAddSqrtNegIsIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
