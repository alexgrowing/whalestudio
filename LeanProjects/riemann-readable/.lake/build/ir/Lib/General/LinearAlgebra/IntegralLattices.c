// Lean compiler output
// Module: Lib.General.LinearAlgebra.IntegralLattices
// Imports: public import Init public meta import Init public import Lib.Adelic.Hecke.Basic public import Lib.General.Groups.BesselGroups
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
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_codRestrict___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_U_cutAt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_subtype___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_U_cutAt___redArg___closed__0 = (const lean_object*)&lp_GRH_New_U_cutAt___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intVectors(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_colLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__0(lean_object* v_toOne_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v_toOne_1_);
return v_toOne_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__0___boxed(lean_object* v_toOne_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_New_cutGL___redArg___lam__0(v_toOne_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_toOne_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg___lam__1(lean_object* v_toSub_6_, lean_object* v_toOne_7_, lean_object* v_e_8_, lean_object* v_toMul_9_, lean_object* v_inst_10_, lean_object* v_toZero_11_, lean_object* v___f_12_, lean_object* v_toAdd_13_, lean_object* v_g_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
lean_inc(v_e_8_);
v___x_17_ = lean_apply_2(v_toSub_6_, v_toOne_7_, v_e_8_);
lean_inc(v___y_16_);
lean_inc(v___y_15_);
v___x_18_ = lean_apply_2(v_g_14_, v___y_15_, v___y_16_);
lean_inc(v_toMul_9_);
v___x_19_ = lean_apply_2(v_toMul_9_, v_e_8_, v___x_18_);
v___x_20_ = lp_mathlib_Matrix_diagonal___redArg(v_inst_10_, v_toZero_11_, v___f_12_, v___y_15_, v___y_16_);
v___x_21_ = lean_apply_2(v_toMul_9_, v___x_17_, v___x_20_);
v___x_22_ = lean_apply_2(v_toAdd_13_, v___x_19_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___redArg(lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_e_25_){
_start:
{
lean_object* v_toSemiring_26_; lean_object* v___x_27_; lean_object* v_toMul_28_; lean_object* v_toAdd_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_toAddMonoidWithOne_32_; lean_object* v_toSub_33_; lean_object* v_toOne_34_; lean_object* v___x_35_; lean_object* v_toZero_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___f_39_; 
v_toSemiring_26_ = lean_ctor_get(v_inst_23_, 0);
lean_inc_ref_n(v_toSemiring_26_, 2);
v___x_27_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_26_);
v_toMul_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_toMul_28_);
v_toAdd_29_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_toAdd_29_);
lean_dec_ref(v___x_27_);
v___x_30_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_23_);
v___x_31_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_30_);
v_toAddMonoidWithOne_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc_ref(v_toAddMonoidWithOne_32_);
lean_dec_ref(v___x_30_);
v_toSub_33_ = lean_ctor_get(v___x_31_, 2);
lean_inc(v_toSub_33_);
lean_dec_ref(v___x_31_);
v_toOne_34_ = lean_ctor_get(v_toAddMonoidWithOne_32_, 2);
lean_inc_n(v_toOne_34_, 2);
lean_dec_ref(v_toAddMonoidWithOne_32_);
v___x_35_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_26_);
v_toZero_36_ = lean_ctor_get(v___x_35_, 1);
lean_inc(v_toZero_36_);
lean_dec_ref(v___x_35_);
v___f_37_ = lean_alloc_closure((void*)(lp_GRH_New_cutGL___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_37_, 0, v_toOne_34_);
v___f_38_ = lean_alloc_closure((void*)(lp_GRH_New_cutGL___redArg___lam__1), 11, 8);
lean_closure_set(v___f_38_, 0, v_toSub_33_);
lean_closure_set(v___f_38_, 1, v_toOne_34_);
lean_closure_set(v___f_38_, 2, v_e_25_);
lean_closure_set(v___f_38_, 3, v_toMul_28_);
lean_closure_set(v___f_38_, 4, v_inst_24_);
lean_closure_set(v___f_38_, 5, v_toZero_36_);
lean_closure_set(v___f_38_, 6, v___f_37_);
lean_closure_set(v___f_38_, 7, v_toAdd_29_);
v___f_39_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_39_, 0, v___f_38_);
return v___f_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cutGL(lean_object* v_A_40_, lean_object* v_inst_41_, lean_object* v_n_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_e_45_, lean_object* v_he_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_GRH_New_cutGL___redArg(v_inst_41_, v_inst_44_, v_e_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cutGL___boxed(lean_object* v_A_48_, lean_object* v_inst_49_, lean_object* v_n_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_e_53_, lean_object* v_he_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_GRH_New_cutGL(v_A_48_, v_inst_49_, v_n_50_, v_inst_51_, v_inst_52_, v_e_53_, v_he_54_);
lean_dec(v_inst_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt___redArg(lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_e_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___f_63_; 
v___x_60_ = lp_GRH_New_cutGL___redArg(v_inst_57_, v_inst_58_, v_e_59_);
v___f_61_ = ((lean_object*)(lp_GRH_New_U_cutAt___redArg___closed__0));
v___f_62_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_62_, 0, v___f_61_);
lean_closure_set(v___f_62_, 1, v___x_60_);
v___f_63_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_codRestrict___redArg___lam__0), 2, 1);
lean_closure_set(v___f_63_, 0, v___f_62_);
return v___f_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt(lean_object* v_A_64_, lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_e_69_, lean_object* v_he_70_, lean_object* v_inst_71_, lean_object* v_hs_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_GRH_New_U_cutAt___redArg(v_inst_65_, v_inst_68_, v_e_69_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_U_cutAt___boxed(lean_object* v_A_74_, lean_object* v_inst_75_, lean_object* v_n_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_e_79_, lean_object* v_he_80_, lean_object* v_inst_81_, lean_object* v_hs_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lp_GRH_New_U_cutAt(v_A_74_, v_inst_75_, v_n_76_, v_inst_77_, v_inst_78_, v_e_79_, v_he_80_, v_inst_81_, v_hs_82_);
lean_dec(v_inst_81_);
lean_dec(v_inst_77_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___redArg(){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___redArg___boxed(lean_object* v___dummy_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_GRH_New_intVectors___redArg();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intVectors(lean_object* v_A_88_, lean_object* v_inst_89_, lean_object* v_R_90_, lean_object* v_n_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_intVectors___boxed(lean_object* v_A_93_, lean_object* v_inst_94_, lean_object* v_R_95_, lean_object* v_n_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_GRH_New_intVectors(v_A_93_, v_inst_94_, v_R_95_, v_n_96_);
lean_dec_ref(v_inst_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___redArg(){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_box(0);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___redArg___boxed(lean_object* v___dummy_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_GRH_New_colLattice___redArg();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_colLattice(lean_object* v_A_102_, lean_object* v_inst_103_, lean_object* v_R_104_, lean_object* v_m_105_, lean_object* v_n_106_, lean_object* v_M_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_colLattice___boxed(lean_object* v_A_110_, lean_object* v_inst_111_, lean_object* v_R_112_, lean_object* v_m_113_, lean_object* v_n_114_, lean_object* v_M_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_GRH_New_colLattice(v_A_110_, v_inst_111_, v_R_112_, v_m_113_, v_n_114_, v_M_115_, v_inst_116_);
lean_dec(v_inst_116_);
lean_dec(v_M_115_);
lean_dec_ref(v_inst_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___redArg(){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___redArg___boxed(lean_object* v___dummy_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = lp_GRH_New_preimageLattice___redArg();
return v_res_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice(lean_object* v_A_122_, lean_object* v_inst_123_, lean_object* v_R_124_, lean_object* v_m_125_, lean_object* v_n_126_, lean_object* v_M_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_preimageLattice___boxed(lean_object* v_A_130_, lean_object* v_inst_131_, lean_object* v_R_132_, lean_object* v_m_133_, lean_object* v_n_134_, lean_object* v_M_135_, lean_object* v_inst_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = lp_GRH_New_preimageLattice(v_A_130_, v_inst_131_, v_R_132_, v_m_133_, v_n_134_, v_M_135_, v_inst_136_);
lean_dec(v_inst_136_);
lean_dec(v_M_135_);
lean_dec_ref(v_inst_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___redArg(){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___redArg___boxed(lean_object* v___dummy_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = lp_GRH_New_unitaryLevel___redArg();
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel(lean_object* v_A_142_, lean_object* v_inst_143_, lean_object* v_R_144_, lean_object* v_n_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_g_148_, lean_object* v_inst_149_, lean_object* v_J_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_unitaryLevel___boxed(lean_object* v_A_152_, lean_object* v_inst_153_, lean_object* v_R_154_, lean_object* v_n_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_g_158_, lean_object* v_inst_159_, lean_object* v_J_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = lp_GRH_New_unitaryLevel(v_A_152_, v_inst_153_, v_R_154_, v_n_155_, v_inst_156_, v_inst_157_, v_g_158_, v_inst_159_, v_J_160_);
lean_dec(v_J_160_);
lean_dec(v_inst_159_);
lean_dec_ref(v_g_158_);
lean_dec_ref(v_inst_157_);
lean_dec(v_inst_156_);
lean_dec_ref(v_inst_153_);
return v_res_161_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Hecke_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Groups_BesselGroups(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_General_LinearAlgebra_IntegralLattices(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Hecke_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Groups_BesselGroups(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
