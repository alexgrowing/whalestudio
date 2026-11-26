// Lean compiler output
// Module: Lib.Weil.Fock.Basic
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.HermitianMatrices public import Lib.General.Measure.HaarModulus public import Lib.General.Measure.IntegralOperators public import Lib.Weil.Construction.WeilOperators
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
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_prodComm___redArg();
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_blockDiagonalRingHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
extern lean_object* lp_mathlib_Complex_instZero;
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1;
static lean_once_cell_t lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Fock_blockMatrix___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_blockMatrix___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Fock_blockMatrix___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_blockMatrix___redArg___closed__1;
static lean_once_cell_t lp_GRH_New_Fock_blockMatrix___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Fock_blockMatrix___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_4_ = lp_mathlib_Complex_ofReal(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_6_ = lp_mathlib_Complex_ofReal(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj___redArg___lam__0(lean_object* v_00_u03b5_7_, lean_object* v_i_8_){
_start:
{
lean_object* v___x_9_; lean_object* v_val_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_9_ = lean_apply_1(v_00_u03b5_7_, v_i_8_);
v_val_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_val_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lean_obj_once(&lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0, &lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__0);
v___x_12_ = lean_int_dec_eq(v_val_10_, v___x_11_);
lean_dec(v_val_10_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
v___x_13_ = lean_obj_once(&lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1, &lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__1);
return v___x_13_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2, &lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2_once, _init_lp_GRH_New_Fock_posProj___redArg___lam__0___closed__2);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj___redArg(lean_object* v_inst_15_, lean_object* v_00_u03b5_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_New_Fock_posProj___redArg___lam__0), 2, 1);
lean_closure_set(v___f_19_, 0, v_00_u03b5_16_);
v___x_20_ = lp_mathlib_Complex_instZero;
v___x_21_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_15_, v___x_20_, v___f_19_, v_a_17_, v_a_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_posProj(lean_object* v_00_u03b9_22_, lean_object* v_inst_23_, lean_object* v_00_u03b5_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_GRH_New_Fock_posProj___redArg(v_inst_23_, v_00_u03b5_24_, v_a_25_, v_a_26_);
return v___x_27_;
}
}
static lean_object* _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__0(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lp_mathlib_Complex_instCommSemiring;
v___x_29_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_mathlib_Equiv_prodComm___redArg();
return v___x_30_;
}
}
static lean_object* _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&lp_GRH_New_Fock_blockMatrix___redArg___closed__1, &lp_GRH_New_Fock_blockMatrix___redArg___closed__1_once, _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__1);
v___x_32_ = lp_mathlib_Matrix_reindex___redArg(v___x_31_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix___redArg(lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_toFun_36_; lean_object* v___x_37_; lean_object* v___f_38_; 
v___x_34_ = lean_obj_once(&lp_GRH_New_Fock_blockMatrix___redArg___closed__0, &lp_GRH_New_Fock_blockMatrix___redArg___closed__0_once, _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__0);
v___x_35_ = lean_obj_once(&lp_GRH_New_Fock_blockMatrix___redArg___closed__2, &lp_GRH_New_Fock_blockMatrix___redArg___closed__2_once, _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__2);
v_toFun_36_ = lean_ctor_get(v___x_35_, 0);
v___x_37_ = lp_mathlib_Matrix_blockDiagonalRingHom___redArg(v_inst_33_, v___x_34_);
lean_inc(v_toFun_36_);
v___f_38_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_38_, 0, v___x_37_);
lean_closure_set(v___f_38_, 1, v_toFun_36_);
return v___f_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix(lean_object* v_00_u03b9_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_T_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_toFun_47_; lean_object* v___x_48_; lean_object* v___f_49_; 
v___x_45_ = lean_obj_once(&lp_GRH_New_Fock_blockMatrix___redArg___closed__0, &lp_GRH_New_Fock_blockMatrix___redArg___closed__0_once, _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__0);
v___x_46_ = lean_obj_once(&lp_GRH_New_Fock_blockMatrix___redArg___closed__2, &lp_GRH_New_Fock_blockMatrix___redArg___closed__2_once, _init_lp_GRH_New_Fock_blockMatrix___redArg___closed__2);
v_toFun_47_ = lean_ctor_get(v___x_46_, 0);
v___x_48_ = lp_mathlib_Matrix_blockDiagonalRingHom___redArg(v_inst_44_, v___x_45_);
lean_inc(v_toFun_47_);
v___f_49_ = lean_alloc_closure((void*)(lp_mathlib_RingHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_49_, 0, v___x_48_);
lean_closure_set(v___f_49_, 1, v_toFun_47_);
return v___f_49_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Fock_blockMatrix___boxed(lean_object* v_00_u03b9_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_T_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lp_GRH_New_Fock_blockMatrix(v_00_u03b9_50_, v_inst_51_, v_inst_52_, v_T_53_, v_inst_54_, v_inst_55_);
lean_dec(v_inst_54_);
lean_dec_ref(v_inst_52_);
lean_dec(v_inst_51_);
return v_res_56_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_HermitianMatrices(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_HaarModulus(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Measure_IntegralOperators(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_Construction_WeilOperators(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Weil_Fock_Basic(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_HermitianMatrices(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_HaarModulus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Measure_IntegralOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_Construction_WeilOperators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
