// Lean compiler output
// Module: Lib.Weil.Construction.ProductsAndTransport
// Imports: public import Init public meta import Init public import Lib.Weil.Construction.VacuumProjections
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
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__0(lean_object* v_u_1_, lean_object* v_e_2_, lean_object* v_inst_3_, lean_object* v_toMul_4_, lean_object* v_x_5_, lean_object* v_i_6_){
_start:
{
lean_object* v___x_7_; lean_object* v_val_8_; lean_object* v_toFun_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_inc(v_i_6_);
v___x_7_ = lean_apply_1(v_u_1_, v_i_6_);
v_val_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_7_);
v_toFun_9_ = lean_ctor_get(v_e_2_, 0);
lean_inc(v_toFun_9_);
lean_dec_ref(v_e_2_);
v___x_10_ = lean_apply_1(v_toFun_9_, v_i_6_);
v___x_11_ = lean_apply_1(v_x_5_, v___x_10_);
v___x_12_ = lean_apply_1(v_inst_3_, v___x_11_);
v___x_13_ = lean_apply_2(v_toMul_4_, v_val_8_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__1(lean_object* v_e_14_, lean_object* v_u_15_, lean_object* v_toMul_16_, lean_object* v_inst_17_, lean_object* v_x_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_20_; lean_object* v_toFun_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_inv_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_20_ = lp_mathlib_Equiv_symm___redArg(v_e_14_);
v_toFun_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_toFun_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = lean_apply_1(v_toFun_21_, v___y_19_);
lean_inc(v___x_22_);
v___x_23_ = lean_apply_1(v_u_15_, v___x_22_);
v_inv_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_inv_24_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_apply_1(v_x_18_, v___x_22_);
v___x_26_ = lean_apply_2(v_toMul_16_, v_inv_24_, v___x_25_);
v___x_27_ = lean_apply_1(v_inst_17_, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv___redArg(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_e_30_, lean_object* v_u_31_){
_start:
{
lean_object* v_toSemiring_32_; lean_object* v___x_33_; lean_object* v_toMul_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_43_; 
v_toSemiring_32_ = lean_ctor_get(v_inst_28_, 0);
lean_inc_ref(v_toSemiring_32_);
lean_dec_ref(v_inst_28_);
v___x_33_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_32_);
v_toMul_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_33_, 1);
lean_dec(v_unused_44_);
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_toMul_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___f_38_; lean_object* v___f_39_; lean_object* v___x_41_; 
lean_inc(v_toMul_34_);
lean_inc(v_inst_29_);
lean_inc_ref(v_e_30_);
lean_inc_ref(v_u_31_);
v___f_38_ = lean_alloc_closure((void*)(lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__0), 6, 4);
lean_closure_set(v___f_38_, 0, v_u_31_);
lean_closure_set(v___f_38_, 1, v_e_30_);
lean_closure_set(v___f_38_, 2, v_inst_29_);
lean_closure_set(v___f_38_, 3, v_toMul_34_);
v___f_39_ = lean_alloc_closure((void*)(lp_GRH_New_CoordChange_starCoordEquiv___redArg___lam__1), 6, 4);
lean_closure_set(v___f_39_, 0, v_e_30_);
lean_closure_set(v___f_39_, 1, v_u_31_);
lean_closure_set(v___f_39_, 2, v_toMul_34_);
lean_closure_set(v___f_39_, 3, v_inst_29_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 1, v___f_39_);
lean_ctor_set(v___x_36_, 0, v___f_38_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___f_38_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v___f_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_CoordChange_starCoordEquiv(lean_object* v_00_u03b9_45_, lean_object* v_00_u03ba_46_, lean_object* v_R_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_e_53_, lean_object* v_u_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_GRH_New_CoordChange_starCoordEquiv___redArg(v_inst_48_, v_inst_51_, v_e_53_, v_u_54_);
return v___x_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_VacuumProjections(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Construction_ProductsAndTransport(uint8_t builtin) {
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
res = initialize_GRH_Lib_Weil_Construction_VacuumProjections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
