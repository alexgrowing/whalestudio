// Lean compiler output
// Module: Lib.GaloisRep.Main.SelmerModules
// Imports: public import Init public meta import Init public import Lib.Adelic.Adeles.LocalFactors public import Lib.ClassField.Global.AlbertBrauerHasseNoether public import Lib.Cyclotomic.Voronoi public import Lib.General.Algebra.FittingIdealsAndLengths
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
lean_object* lp_mathlib_Monoid_toMulAction___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_smul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_smulMulHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_RingHom_mapMatrix___redArg(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_prod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_locConst___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_locConst___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_locConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_locConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___redArg(lean_object* v_inst_1_, lean_object* v_e_2_, lean_object* v_00_u03c8_3_, lean_object* v_00_u03c1_4_){
_start:
{
lean_object* v_toSemiring_5_; lean_object* v_toMonoid_6_; lean_object* v___x_7_; lean_object* v___f_8_; lean_object* v___f_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___x_12_; lean_object* v___f_13_; 
v_toSemiring_5_ = lean_ctor_get(v_inst_1_, 0);
v_toMonoid_6_ = lean_ctor_get(v_toSemiring_5_, 1);
v___x_7_ = lp_mathlib_Monoid_toMulAction___redArg(v_toMonoid_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_smul___redArg___lam__0), 5, 1);
lean_closure_set(v___f_8_, 0, v___x_7_);
v___f_9_ = lean_alloc_closure((void*)(lp_mathlib_smulMulHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_9_, 0, v___f_8_);
v___x_10_ = lp_mathlib_RingHom_mapMatrix___redArg(v_e_2_);
v___f_11_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_11_, 0, v_00_u03c1_4_);
lean_closure_set(v___f_11_, 1, v___x_10_);
v___x_12_ = lp_mathlib_MonoidHom_prod___redArg(v_00_u03c8_3_, v___f_11_);
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v___x_12_);
lean_closure_set(v___f_13_, 1, v___f_9_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___redArg___boxed(lean_object* v_inst_14_, lean_object* v_e_15_, lean_object* v_00_u03c8_16_, lean_object* v_00_u03c1_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_GRH_New_twistRep___redArg(v_inst_14_, v_e_15_, v_00_u03c8_16_, v_00_u03c1_17_);
lean_dec_ref(v_inst_14_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistRep(lean_object* v_G_19_, lean_object* v_O_20_, lean_object* v_O_x27_21_, lean_object* v_n_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_e_28_, lean_object* v_00_u03c8_29_, lean_object* v_00_u03c1_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_GRH_New_twistRep___redArg(v_inst_24_, v_e_28_, v_00_u03c8_29_, v_00_u03c1_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_twistRep___boxed(lean_object* v_G_32_, lean_object* v_O_33_, lean_object* v_O_x27_34_, lean_object* v_n_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_e_41_, lean_object* v_00_u03c8_42_, lean_object* v_00_u03c1_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_twistRep(v_G_32_, v_O_33_, v_O_x27_34_, v_n_35_, v_inst_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_e_41_, v_00_u03c8_42_, v_00_u03c1_43_);
lean_dec_ref(v_inst_40_);
lean_dec_ref(v_inst_39_);
lean_dec(v_inst_38_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_36_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_locConst___redArg(){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_locConst___redArg___boxed(lean_object* v___dummy_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_locConst___redArg();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_locConst(lean_object* v_G_49_, lean_object* v_O_50_, lean_object* v_inst_51_, lean_object* v_B_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_box(0);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_locConst___boxed(lean_object* v_G_57_, lean_object* v_O_58_, lean_object* v_inst_59_, lean_object* v_B_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_locConst(v_G_57_, v_O_58_, v_inst_59_, v_B_60_, v_inst_61_, v_inst_62_, v_inst_63_);
lean_dec(v_inst_62_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_Selmer_shaOdd___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd(lean_object* v_00_u2113_69_, lean_object* v_inst_70_, lean_object* v_E_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_inst_74_, lean_object* v_00_u039b_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_e_78_, lean_object* v_00_u03bd_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_shaOdd___boxed(lean_object* v_00_u2113_81_, lean_object* v_inst_82_, lean_object* v_E_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_00_u039b_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_e_90_, lean_object* v_00_u03bd_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_GRH_New_Selmer_shaOdd(v_00_u2113_81_, v_inst_82_, v_E_83_, v_inst_84_, v_inst_85_, v_inst_86_, v_00_u039b_87_, v_inst_88_, v_inst_89_, v_e_90_, v_00_u03bd_91_);
lean_dec(v_00_u03bd_91_);
lean_dec(v_e_90_);
lean_dec_ref(v_inst_89_);
lean_dec_ref(v_inst_88_);
lean_dec_ref(v_inst_85_);
lean_dec_ref(v_inst_84_);
lean_dec(v_00_u2113_81_);
return v_res_92_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Adeles_LocalFactors(uint8_t builtin);
lean_object* initialize_GRH_Lib_ClassField_Global_AlbertBrauerHasseNoether(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cyclotomic_Voronoi(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_FittingIdealsAndLengths(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_GaloisRep_Main_SelmerModules(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Adeles_LocalFactors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_ClassField_Global_AlbertBrauerHasseNoether(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cyclotomic_Voronoi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_FittingIdealsAndLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
