// Lean compiler output
// Module: Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Divisibility.LiftLat public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas public import Formalism.LocalToGlobal.Divisibility.ProjLemmas public import Formalism.LocalToGlobal.Divisibility.FramesLemmas public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
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
lean_object* lp_tree_Formalism_L2_Col_gaussBin(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_instNatCast___lam__0(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___boxed(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__1_value;
static const lean_ctor_object lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__2 = (const lean_object*)&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = l_Rat_instNatCast___lam__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0(lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0, &lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__0___closed__0);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1(lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0, &lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0_once, _init_lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___closed__0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1___boxed(lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___lam__1(v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg(lean_object* v_P_18_){
_start:
{
lean_object* v___f_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___f_19_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__1));
v___x_20_ = ((lean_object*)(lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg___closed__2));
v___x_21_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_P_18_);
lean_ctor_set(v___x_21_, 2, v___f_19_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel(lean_object* v_G_22_, lean_object* v_inst_23_, lean_object* v_P_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___redArg(v_P_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel___boxed(lean_object* v_G_26_, lean_object* v_inst_27_, lean_object* v_P_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_tree_Formalism_L2_DIV_LiftTest_trivialCharacterLevel(v_G_26_, v_inst_27_, v_P_28_);
lean_dec_ref(v_inst_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg(lean_object* v_i_30_){
_start:
{
lean_object* v_snd_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_snd_31_ = lean_ctor_get(v_i_30_, 1);
v___x_32_ = lean_unsigned_to_nat(2u);
v___x_33_ = lp_tree_Formalism_L2_Col_gaussBin(v___x_32_, v___x_32_, v_snd_31_);
v___x_34_ = l_Rat_instNatCast___lam__0(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg___boxed(lean_object* v_i_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg(v_i_35_);
lean_dec_ref(v_i_35_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX(lean_object* v_G_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_i_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_tree_Formalism_L2_DIV_LiftTest_toyX___redArg(v_i_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_DIV_LiftTest_toyX___boxed(lean_object* v_G_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_i_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_tree_Formalism_L2_DIV_LiftTest_toyX(v_G_42_, v_inst_43_, v_inst_44_, v_i_45_);
lean_dec_ref(v_i_45_);
lean_dec(v_inst_44_);
lean_dec_ref(v_inst_43_);
return v_res_46_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLatLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_ProjLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_FramesLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(uint8_t builtin);
lean_object* initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLatLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_LiftLat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_RowLatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_ProjLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Divisibility_FramesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
