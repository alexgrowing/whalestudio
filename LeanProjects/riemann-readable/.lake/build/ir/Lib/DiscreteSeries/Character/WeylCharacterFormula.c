// Lean compiler output
// Module: Lib.DiscreteSeries.Character.WeylCharacterFormula
// Imports: public import Init public meta import Init public import Lib.GLn.SchurModule.SchurOrthogonality public import Lib.General.LinearAlgebra.Eigenvalues
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
uint8_t lp_mathlib_Units_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lp_mathlib_Multiset_product___redArg(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1;
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_HCParam_lowerCount___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_obj_once(&lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0, &lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__0);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__0(lean_object* v_00_u03b5_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_7_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_8_ = lean_apply_1(v_00_u03b5_5_, v_a_6_);
v___x_9_ = lean_obj_once(&lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1, &lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1);
v___x_10_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_7_, v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 1;
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___boxed(lean_object* v_00_u03b5_13_, lean_object* v_a_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = lp_GRH_New_Orbital_oppositePairs___redArg___lam__0(v_00_u03b5_13_, v_a_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_Orbital_oppositePairs___redArg___lam__1(lean_object* v_00_u03b5_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_19_ = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
v___x_20_ = lean_apply_1(v_00_u03b5_17_, v_a_18_);
v___x_21_ = lean_obj_once(&lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1, &lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___closed__1);
v___x_22_ = lp_mathlib_Units_instDecidableEq___redArg(v___x_19_, v___x_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg___lam__1___boxed(lean_object* v_00_u03b5_23_, lean_object* v_a_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = lp_GRH_New_Orbital_oppositePairs___redArg___lam__1(v_00_u03b5_23_, v_a_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs___redArg(lean_object* v_inst_27_, lean_object* v_00_u03b5_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_inc_ref(v_00_u03b5_28_);
v___f_29_ = lean_alloc_closure((void*)(lp_GRH_New_Orbital_oppositePairs___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_29_, 0, v_00_u03b5_28_);
v___f_30_ = lean_alloc_closure((void*)(lp_GRH_New_Orbital_oppositePairs___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_30_, 0, v_00_u03b5_28_);
lean_inc(v_inst_27_);
v___x_31_ = lp_mathlib_Multiset_filter___redArg(v___f_30_, v_inst_27_);
v___x_32_ = lp_mathlib_Multiset_filter___redArg(v___f_29_, v_inst_27_);
v___x_33_ = lp_mathlib_Multiset_product___redArg(v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_oppositePairs(lean_object* v_n_34_, lean_object* v_inst_35_, lean_object* v_00_u03b5_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_GRH_New_Orbital_oppositePairs___redArg(v_inst_35_, v_00_u03b5_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___redArg(){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lp_GRH_New_Orbital_leadingMonomials___redArg();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials(lean_object* v_n_42_, lean_object* v_inst_43_, lean_object* v_l_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Orbital_leadingMonomials___boxed(lean_object* v_n_46_, lean_object* v_inst_47_, lean_object* v_l_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_GRH_New_Orbital_leadingMonomials(v_n_46_, v_inst_47_, v_l_48_);
lean_dec_ref(v_l_48_);
lean_dec(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_HCParam_lowerCount___redArg___lam__0(lean_object* v_00_u03b5_50_, lean_object* v_a_51_, lean_object* v_inst_52_, lean_object* v_l_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
lean_inc_ref(v_00_u03b5_50_);
lean_inc(v_a_51_);
v___x_55_ = lean_apply_1(v_00_u03b5_50_, v_a_51_);
lean_inc(v_a_54_);
v___x_56_ = lean_apply_1(v_00_u03b5_50_, v_a_54_);
v___x_57_ = lean_apply_2(v_inst_52_, v___x_55_, v___x_56_);
v___x_58_ = lean_unbox(v___x_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
lean_dec(v_a_54_);
lean_dec_ref(v_l_53_);
lean_dec(v_a_51_);
v___x_59_ = lean_unbox(v___x_57_);
return v___x_59_;
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
lean_inc_ref(v_l_53_);
v___x_60_ = lean_apply_1(v_l_53_, v_a_54_);
v___x_61_ = lean_apply_1(v_l_53_, v_a_51_);
v___x_62_ = lean_int_dec_lt(v___x_60_, v___x_61_);
lean_dec(v___x_61_);
lean_dec(v___x_60_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount___redArg___lam__0___boxed(lean_object* v_00_u03b5_63_, lean_object* v_a_64_, lean_object* v_inst_65_, lean_object* v_l_66_, lean_object* v_a_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = lp_GRH_New_HCParam_lowerCount___redArg___lam__0(v_00_u03b5_63_, v_a_64_, v_inst_65_, v_l_66_, v_a_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount___redArg(lean_object* v_inst_70_, lean_object* v_00_u03b5_71_, lean_object* v_l_72_, lean_object* v_inst_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___f_75_ = lean_alloc_closure((void*)(lp_GRH_New_HCParam_lowerCount___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_75_, 0, v_00_u03b5_71_);
lean_closure_set(v___f_75_, 1, v_a_74_);
lean_closure_set(v___f_75_, 2, v_inst_73_);
lean_closure_set(v___f_75_, 3, v_l_72_);
v___x_76_ = lp_mathlib_Multiset_filter___redArg(v___f_75_, v_inst_70_);
v___x_77_ = l_List_lengthTR___redArg(v___x_76_);
lean_dec(v___x_76_);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_HCParam_lowerCount(lean_object* v_n_79_, lean_object* v_inst_80_, lean_object* v_00_u03b5_81_, lean_object* v_l_82_, lean_object* v_r_83_, lean_object* v_inst_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_GRH_New_HCParam_lowerCount___redArg(v_inst_80_, v_00_u03b5_81_, v_l_82_, v_inst_84_, v_a_85_);
return v___x_86_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_GLn_SchurModule_SchurOrthogonality(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Character_WeylCharacterFormula(uint8_t builtin) {
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
res = initialize_GRH_Lib_GLn_SchurModule_SchurOrthogonality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_Eigenvalues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
