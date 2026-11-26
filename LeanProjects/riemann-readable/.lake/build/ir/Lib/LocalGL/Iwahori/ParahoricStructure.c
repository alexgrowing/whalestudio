// Lean compiler output
// Module: Lib.LocalGL.Iwahori.ParahoricStructure
// Imports: public import Init public meta import Init public import Lib.Adelic.Hecke.ClassSums public import Lib.General.LinearAlgebra.HermiteForm
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
lean_object* lp_mathlib_Equiv_Perm_permGroup___redArg();
lean_object* lp_mathlib_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_permMatrixHom___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_toHomUnits___redArg(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_mathlib_MulOneClass_toMulOne___redArg(lean_object*);
lean_object* lp_GRH_New_diagGL___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_MulAut_conj___redArg(lean_object*);
lean_object* lp_mathlib_MulEquiv_symm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_npowRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_zpowRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_MulEquiv_comapSubgroup___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_toEmbedding___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semiring_toNonUnitalSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Representation_subrepresentation___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_permGL___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_permGL___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_permGL___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_permGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_permGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__0 = (const lean_object*)&lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__0_value;
static lean_once_cell_t lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1;
static lean_once_cell_t lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_permGL___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lp_mathlib_Equiv_Perm_permGroup___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permGL___redArg(lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; lean_object* v_toSemiring_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_permGL___redArg___closed__0, &lp_GRH_New_permGL___redArg___closed__0_once, _init_lp_GRH_New_permGL___redArg___closed__0);
v_toSemiring_5_ = lean_ctor_get(v_inst_3_, 0);
lean_inc_ref(v_toSemiring_5_);
lean_dec_ref(v_inst_3_);
v___x_6_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_5_);
v___x_7_ = lp_mathlib_Matrix_permMatrixHom___redArg(v_inst_2_, v___x_6_);
v___x_8_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_4_, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permGL(lean_object* v_n_9_, lean_object* v_R_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; lean_object* v_toSemiring_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_14_ = lean_obj_once(&lp_GRH_New_permGL___redArg___closed__0, &lp_GRH_New_permGL___redArg___closed__0_once, _init_lp_GRH_New_permGL___redArg___closed__0);
v_toSemiring_15_ = lean_ctor_get(v_inst_13_, 0);
lean_inc_ref(v_toSemiring_15_);
lean_dec_ref(v_inst_13_);
v___x_16_ = lp_mathlib_Semiring_toNonAssocSemiring___redArg(v_toSemiring_15_);
v___x_17_ = lp_mathlib_Matrix_permMatrixHom___redArg(v_inst_12_, v___x_16_);
v___x_18_ = lp_mathlib_MonoidHom_toHomUnits___redArg(v___x_14_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_permGL___boxed(lean_object* v_n_19_, lean_object* v_R_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_GRH_New_permGL(v_n_19_, v_R_20_, v_inst_21_, v_inst_22_, v_inst_23_);
lean_dec(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___redArg(){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___redArg___boxed(lean_object* v___dummy_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lp_GRH_New_residuePreimage___redArg();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage(lean_object* v_n_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_F_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_P_35_, lean_object* v_H_36_, lean_object* v_e_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_residuePreimage___boxed(lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_F_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_P_45_, lean_object* v_H_46_, lean_object* v_e_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_residuePreimage(v_n_39_, v_inst_40_, v_inst_41_, v_F_42_, v_inst_43_, v_inst_44_, v_P_45_, v_H_46_, v_e_47_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_41_);
lean_dec(v_inst_40_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___redArg(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___redArg___boxed(lean_object* v___dummy_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_GRH_New_blockParahoric___redArg();
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric(lean_object* v_F_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_N_56_, lean_object* v_b_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_blockParahoric___boxed(lean_object* v_F_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_N_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_blockParahoric(v_F_59_, v_inst_60_, v_inst_61_, v_N_62_, v_b_63_);
lean_dec_ref(v_b_63_);
lean_dec(v_N_62_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_dominantTorus___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus(lean_object* v_n_69_, lean_object* v_F_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_dominantTorus___boxed(lean_object* v_n_75_, lean_object* v_F_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_inst_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_GRH_New_dominantTorus(v_n_75_, v_F_76_, v_inst_77_, v_inst_78_, v_inst_79_);
lean_dec_ref(v_inst_79_);
lean_dec_ref(v_inst_78_);
lean_dec_ref(v_inst_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___redArg(){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = lp_GRH_New_proIwahori___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori(lean_object* v_n_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_F_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_proIwahori___boxed(lean_object* v_n_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_F_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_GRH_New_proIwahori(v_n_93_, v_inst_94_, v_inst_95_, v_F_96_, v_inst_97_, v_inst_98_, v_inst_99_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
lean_dec_ref(v_inst_97_);
lean_dec_ref(v_inst_95_);
lean_dec(v_inst_94_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___redArg(){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___redArg___boxed(lean_object* v___dummy_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_GRH_New_cyclicSpan___redArg();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan(lean_object* v_G_105_, lean_object* v_V_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_00_u03c1_110_, lean_object* v_y_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_cyclicSpan___boxed(lean_object* v_G_113_, lean_object* v_V_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_00_u03c1_118_, lean_object* v_y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = lp_GRH_New_cyclicSpan(v_G_113_, v_V_114_, v_inst_115_, v_inst_116_, v_inst_117_, v_00_u03c1_118_, v_y_119_);
lean_dec(v_y_119_);
lean_dec(v_00_u03c1_118_);
lean_dec(v_inst_117_);
lean_dec_ref(v_inst_116_);
lean_dec_ref(v_inst_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___redArg(){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___redArg___boxed(lean_object* v___dummy_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_GRH_New_smoothVectors___redArg();
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors(lean_object* v_G_125_, lean_object* v_V_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_00_u03c1_130_, lean_object* v_inst_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectors___boxed(lean_object* v_G_133_, lean_object* v_V_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_00_u03c1_138_, lean_object* v_inst_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_GRH_New_smoothVectors(v_G_133_, v_V_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_00_u03c1_138_, v_inst_139_);
lean_dec(v_00_u03c1_138_);
lean_dec(v_inst_137_);
lean_dec_ref(v_inst_136_);
lean_dec_ref(v_inst_135_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep___redArg(lean_object* v_00_u03c1_141_){
_start:
{
lean_object* v___f_142_; 
v___f_142_ = lean_alloc_closure((void*)(lp_mathlib_Representation_subrepresentation___redArg___lam__0), 3, 1);
lean_closure_set(v___f_142_, 0, v_00_u03c1_141_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep(lean_object* v_G_143_, lean_object* v_V_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_00_u03c1_148_, lean_object* v_inst_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v___f_151_; 
v___f_151_ = lean_alloc_closure((void*)(lp_mathlib_Representation_subrepresentation___redArg___lam__0), 3, 1);
lean_closure_set(v___f_151_, 0, v_00_u03c1_148_);
return v___f_151_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_smoothVectorRep___boxed(lean_object* v_G_152_, lean_object* v_V_153_, lean_object* v_inst_154_, lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_00_u03c1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = lp_GRH_New_smoothVectorRep(v_G_152_, v_V_153_, v_inst_154_, v_inst_155_, v_inst_156_, v_00_u03c1_157_, v_inst_158_, v_inst_159_);
lean_dec(v_inst_156_);
lean_dec_ref(v_inst_155_);
lean_dec_ref(v_inst_154_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___lam__0(lean_object* v_g_161_, lean_object* v_h_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lp_mathlib_Equiv_trans___redArg(v_h_162_, v_g_161_);
return v___x_163_;
}
}
static lean_object* _init_lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1(void){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lp_mathlib_Equiv_refl___redArg();
return v___x_165_;
}
}
static lean_object* _init_lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2(void){
_start:
{
lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___f_166_ = ((lean_object*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__0));
v___x_167_ = lean_obj_once(&lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1, &lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1_once, _init_lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__1);
v___x_168_ = lean_alloc_closure((void*)(l_npowRec___boxed), 5, 3);
lean_closure_set(v___x_168_, 0, lean_box(0));
lean_closure_set(v___x_168_, 1, v___x_167_);
lean_closure_set(v___x_168_, 2, v___f_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg(lean_object* v_N_169_, lean_object* v_inst_170_, lean_object* v_t_171_, lean_object* v_j_172_){
_start:
{
lean_object* v_toCommRing_173_; lean_object* v_toSemiring_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_toMonoid_178_; lean_object* v___x_179_; lean_object* v_toMonoid_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_toMul_183_; lean_object* v___x_92__overap_184_; lean_object* v___x_185_; lean_object* v___x_95__overap_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_toCommRing_173_ = lean_ctor_get(v_inst_170_, 0);
lean_inc_ref(v_toCommRing_173_);
lean_dec_ref(v_inst_170_);
v_toSemiring_174_ = lean_ctor_get(v_toCommRing_173_, 0);
lean_inc(v_N_169_);
v___x_175_ = l_List_finRange(v_N_169_);
v___x_176_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_176_, 0, v_N_169_);
lean_inc_ref(v___x_176_);
lean_inc_ref(v_toSemiring_174_);
v___x_177_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_174_, v___x_175_, v___x_176_);
v_toMonoid_178_ = lean_ctor_get(v___x_177_, 1);
lean_inc_ref(v_toMonoid_178_);
lean_dec_ref(v___x_177_);
v___x_179_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_178_);
v_toMonoid_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_toMonoid_180_);
v___x_181_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_180_);
lean_dec_ref(v_toMonoid_180_);
v___x_182_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_181_);
v_toMul_183_ = lean_ctor_get(v___x_182_, 1);
lean_inc_n(v_toMul_183_, 2);
lean_dec_ref(v___x_182_);
v___x_92__overap_184_ = lp_GRH_New_diagGL___redArg(v___x_176_, v_toCommRing_173_);
v___x_185_ = lean_apply_1(v___x_92__overap_184_, v_t_171_);
v___x_95__overap_186_ = lp_mathlib_MulAut_conj___redArg(v___x_179_);
v___x_187_ = lean_apply_1(v___x_95__overap_186_, v___x_185_);
v___x_188_ = lean_alloc_closure((void*)(lp_mathlib_MulEquiv_symm___boxed), 5, 4);
lean_closure_set(v___x_188_, 0, lean_box(0));
lean_closure_set(v___x_188_, 1, lean_box(0));
lean_closure_set(v___x_188_, 2, v_toMul_183_);
lean_closure_set(v___x_188_, 3, v_toMul_183_);
v___x_189_ = lean_obj_once(&lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2, &lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2_once, _init_lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2);
v___x_190_ = lp_mathlib_zpowRec___redArg(v___x_188_, v___x_189_, v_j_172_, v___x_187_);
lean_inc_ref(v___x_179_);
v___x_191_ = lp_mathlib_MulEquiv_comapSubgroup___redArg(v___x_179_, v___x_179_, v___x_190_);
v___x_192_ = lean_box(0);
v___x_193_ = lp_mathlib_Equiv_toEmbedding___redArg___lam__0(v___x_191_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___boxed(lean_object* v_N_194_, lean_object* v_inst_195_, lean_object* v_t_196_, lean_object* v_j_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg(v_N_194_, v_inst_195_, v_t_196_, v_j_197_);
lean_dec(v_j_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori(lean_object* v_F_199_, lean_object* v_N_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_t_203_, lean_object* v_j_204_){
_start:
{
lean_object* v_toCommRing_205_; lean_object* v_toSemiring_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_toMonoid_210_; lean_object* v___x_211_; lean_object* v_toMonoid_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_toMul_215_; lean_object* v___x_133__overap_216_; lean_object* v___x_217_; lean_object* v___x_134__overap_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_toCommRing_205_ = lean_ctor_get(v_inst_201_, 0);
lean_inc_ref(v_toCommRing_205_);
lean_dec_ref(v_inst_201_);
v_toSemiring_206_ = lean_ctor_get(v_toCommRing_205_, 0);
lean_inc(v_N_200_);
v___x_207_ = l_List_finRange(v_N_200_);
v___x_208_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_208_, 0, v_N_200_);
lean_inc_ref(v___x_208_);
lean_inc_ref(v_toSemiring_206_);
v___x_209_ = lp_mathlib_Matrix_semiring___redArg(v_toSemiring_206_, v___x_207_, v___x_208_);
v_toMonoid_210_ = lean_ctor_get(v___x_209_, 1);
lean_inc_ref(v_toMonoid_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_210_);
v_toMonoid_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_toMonoid_212_);
v___x_213_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_212_);
lean_dec_ref(v_toMonoid_212_);
v___x_214_ = lp_mathlib_MulOneClass_toMulOne___redArg(v___x_213_);
v_toMul_215_ = lean_ctor_get(v___x_214_, 1);
lean_inc_n(v_toMul_215_, 2);
lean_dec_ref(v___x_214_);
v___x_133__overap_216_ = lp_GRH_New_diagGL___redArg(v___x_208_, v_toCommRing_205_);
v___x_217_ = lean_apply_1(v___x_133__overap_216_, v_t_203_);
v___x_134__overap_218_ = lp_mathlib_MulAut_conj___redArg(v___x_211_);
v___x_219_ = lean_apply_1(v___x_134__overap_218_, v___x_217_);
v___x_220_ = lean_alloc_closure((void*)(lp_mathlib_MulEquiv_symm___boxed), 5, 4);
lean_closure_set(v___x_220_, 0, lean_box(0));
lean_closure_set(v___x_220_, 1, lean_box(0));
lean_closure_set(v___x_220_, 2, v_toMul_215_);
lean_closure_set(v___x_220_, 3, v_toMul_215_);
v___x_221_ = lean_obj_once(&lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2, &lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2_once, _init_lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___redArg___closed__2);
v___x_222_ = lp_mathlib_zpowRec___redArg(v___x_220_, v___x_221_, v_j_204_, v___x_219_);
lean_inc_ref(v___x_211_);
v___x_223_ = lp_mathlib_MulEquiv_comapSubgroup___redArg(v___x_211_, v___x_211_, v___x_222_);
v___x_224_ = lean_box(0);
v___x_225_ = lp_mathlib_Equiv_toEmbedding___redArg___lam__0(v___x_223_, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori___boxed(lean_object* v_F_226_, lean_object* v_N_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_t_230_, lean_object* v_j_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_conjProIwahori(v_F_226_, v_N_227_, v_inst_228_, v_inst_229_, v_t_230_, v_j_231_);
lean_dec(v_j_231_);
lean_dec_ref(v_inst_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__0(lean_object* v_val_233_, lean_object* v___y_234_, lean_object* v_j_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_apply_2(v_val_233_, v_j_235_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__1(lean_object* v_inv_237_, lean_object* v_j_238_, lean_object* v_j_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_apply_2(v_inv_237_, v_j_238_, v_j_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__2(lean_object* v_val_241_, lean_object* v_j_242_, lean_object* v_j_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_apply_2(v_val_241_, v_j_243_, v_j_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3(lean_object* v_val_245_, lean_object* v___x_246_, lean_object* v_toMul_247_, lean_object* v_toAddCommMonoid_248_, lean_object* v___f_249_, lean_object* v_j_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; 
v___f_251_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__2), 3, 2);
lean_closure_set(v___f_251_, 0, v_val_245_);
lean_closure_set(v___f_251_, 1, v_j_250_);
v___x_252_ = lp_mathlib_dotProduct___redArg(v___x_246_, v_toMul_247_, v_toAddCommMonoid_248_, v___f_249_, v___f_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3___boxed(lean_object* v_val_253_, lean_object* v___x_254_, lean_object* v_toMul_255_, lean_object* v_toAddCommMonoid_256_, lean_object* v___f_257_, lean_object* v_j_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3(v_val_253_, v___x_254_, v_toMul_255_, v_toAddCommMonoid_256_, v___f_257_, v_j_258_);
lean_dec_ref(v_toAddCommMonoid_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__4(lean_object* v_inv_260_, lean_object* v_val_261_, lean_object* v___x_262_, lean_object* v_toMul_263_, lean_object* v_toAddCommMonoid_264_, lean_object* v___f_265_, lean_object* v_j_266_){
_start:
{
lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___x_269_; 
v___f_267_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__1), 3, 2);
lean_closure_set(v___f_267_, 0, v_inv_260_);
lean_closure_set(v___f_267_, 1, v_j_266_);
lean_inc_ref(v_toAddCommMonoid_264_);
lean_inc(v_toMul_263_);
lean_inc(v___x_262_);
v___f_268_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_268_, 0, v_val_261_);
lean_closure_set(v___f_268_, 1, v___x_262_);
lean_closure_set(v___f_268_, 2, v_toMul_263_);
lean_closure_set(v___f_268_, 3, v_toAddCommMonoid_264_);
lean_closure_set(v___f_268_, 4, v___f_267_);
v___x_269_ = lp_mathlib_dotProduct___redArg(v___x_262_, v_toMul_263_, v_toAddCommMonoid_264_, v___f_268_, v___f_265_);
lean_dec_ref(v_toAddCommMonoid_264_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__5(lean_object* v_inv_270_, lean_object* v___y_271_, lean_object* v_j_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_apply_2(v_inv_270_, v___y_271_, v_j_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6(lean_object* v_val_274_, lean_object* v_inv_275_, lean_object* v_val_276_, lean_object* v___x_277_, lean_object* v_toMul_278_, lean_object* v_toAddCommMonoid_279_, lean_object* v_inv_280_, lean_object* v_toMul_281_, lean_object* v_toAddCommMonoid_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_285_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_285_, 0, v_val_274_);
lean_closure_set(v___f_285_, 1, v___y_284_);
lean_inc(v___x_277_);
v___f_286_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__4), 7, 6);
lean_closure_set(v___f_286_, 0, v_inv_275_);
lean_closure_set(v___f_286_, 1, v_val_276_);
lean_closure_set(v___f_286_, 2, v___x_277_);
lean_closure_set(v___f_286_, 3, v_toMul_278_);
lean_closure_set(v___f_286_, 4, v_toAddCommMonoid_279_);
lean_closure_set(v___f_286_, 5, v___f_285_);
v___f_287_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__5), 3, 2);
lean_closure_set(v___f_287_, 0, v_inv_280_);
lean_closure_set(v___f_287_, 1, v___y_283_);
v___x_288_ = lp_mathlib_dotProduct___redArg(v___x_277_, v_toMul_281_, v_toAddCommMonoid_282_, v___f_287_, v___f_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6___boxed(lean_object* v_val_289_, lean_object* v_inv_290_, lean_object* v_val_291_, lean_object* v___x_292_, lean_object* v_toMul_293_, lean_object* v_toAddCommMonoid_294_, lean_object* v_inv_295_, lean_object* v_toMul_296_, lean_object* v_toAddCommMonoid_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6(v_val_289_, v_inv_290_, v_val_291_, v___x_292_, v_toMul_293_, v_toAddCommMonoid_294_, v_inv_295_, v_toMul_296_, v_toAddCommMonoid_297_, v___y_298_, v___y_299_);
lean_dec_ref(v_toAddCommMonoid_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11(lean_object* v_inv_301_, lean_object* v___x_302_, lean_object* v_toMul_303_, lean_object* v_toAddCommMonoid_304_, lean_object* v___f_305_, lean_object* v_j_306_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; 
v___f_307_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__1), 3, 2);
lean_closure_set(v___f_307_, 0, v_inv_301_);
lean_closure_set(v___f_307_, 1, v_j_306_);
v___x_308_ = lp_mathlib_dotProduct___redArg(v___x_302_, v_toMul_303_, v_toAddCommMonoid_304_, v___f_307_, v___f_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11___boxed(lean_object* v_inv_309_, lean_object* v___x_310_, lean_object* v_toMul_311_, lean_object* v_toAddCommMonoid_312_, lean_object* v___f_313_, lean_object* v_j_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11(v_inv_309_, v___x_310_, v_toMul_311_, v_toAddCommMonoid_312_, v___f_313_, v_j_314_);
lean_dec_ref(v_toAddCommMonoid_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__7(lean_object* v_val_316_, lean_object* v_inv_317_, lean_object* v___x_318_, lean_object* v_toMul_319_, lean_object* v_toAddCommMonoid_320_, lean_object* v___f_321_, lean_object* v_j_322_){
_start:
{
lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___x_325_; 
v___f_323_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__2), 3, 2);
lean_closure_set(v___f_323_, 0, v_val_316_);
lean_closure_set(v___f_323_, 1, v_j_322_);
lean_inc_ref(v_toAddCommMonoid_320_);
lean_inc(v_toMul_319_);
lean_inc(v___x_318_);
v___f_324_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__11___boxed), 6, 5);
lean_closure_set(v___f_324_, 0, v_inv_317_);
lean_closure_set(v___f_324_, 1, v___x_318_);
lean_closure_set(v___f_324_, 2, v_toMul_319_);
lean_closure_set(v___f_324_, 3, v_toAddCommMonoid_320_);
lean_closure_set(v___f_324_, 4, v___f_323_);
v___x_325_ = lp_mathlib_dotProduct___redArg(v___x_318_, v_toMul_319_, v_toAddCommMonoid_320_, v___f_321_, v___f_324_);
lean_dec_ref(v_toAddCommMonoid_320_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8(lean_object* v_val_326_, lean_object* v_inv_327_, lean_object* v_val_328_, lean_object* v_inv_329_, lean_object* v___x_330_, lean_object* v_toMul_331_, lean_object* v_toAddCommMonoid_332_, lean_object* v_toMul_333_, lean_object* v_toAddCommMonoid_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v___f_337_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__0), 3, 2);
lean_closure_set(v___f_337_, 0, v_val_326_);
lean_closure_set(v___f_337_, 1, v___y_336_);
v___f_338_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__5), 3, 2);
lean_closure_set(v___f_338_, 0, v_inv_327_);
lean_closure_set(v___f_338_, 1, v___y_335_);
lean_inc(v___x_330_);
v___f_339_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__7), 7, 6);
lean_closure_set(v___f_339_, 0, v_val_328_);
lean_closure_set(v___f_339_, 1, v_inv_329_);
lean_closure_set(v___f_339_, 2, v___x_330_);
lean_closure_set(v___f_339_, 3, v_toMul_331_);
lean_closure_set(v___f_339_, 4, v_toAddCommMonoid_332_);
lean_closure_set(v___f_339_, 5, v___f_338_);
v___x_340_ = lp_mathlib_dotProduct___redArg(v___x_330_, v_toMul_333_, v_toAddCommMonoid_334_, v___f_339_, v___f_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8___boxed(lean_object* v_val_341_, lean_object* v_inv_342_, lean_object* v_val_343_, lean_object* v_inv_344_, lean_object* v___x_345_, lean_object* v_toMul_346_, lean_object* v_toAddCommMonoid_347_, lean_object* v_toMul_348_, lean_object* v_toAddCommMonoid_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8(v_val_341_, v_inv_342_, v_val_343_, v_inv_344_, v___x_345_, v_toMul_346_, v_toAddCommMonoid_347_, v_toMul_348_, v_toAddCommMonoid_349_, v___y_350_, v___y_351_);
lean_dec_ref(v_toAddCommMonoid_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg(lean_object* v_N_353_, lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_g_356_, lean_object* v_00_u03c3_357_, lean_object* v_k_358_){
_start:
{
lean_object* v_toCommRing_359_; lean_object* v_toSemiring_360_; lean_object* v___x_361_; lean_object* v_toCommSemiring_362_; lean_object* v___x_363_; lean_object* v___x_335__overap_364_; lean_object* v___x_365_; lean_object* v_val_366_; lean_object* v_inv_367_; lean_object* v_val_368_; lean_object* v_inv_369_; lean_object* v_val_370_; lean_object* v_inv_371_; lean_object* v___x_372_; lean_object* v_toAddCommMonoid_373_; lean_object* v___x_374_; lean_object* v_toMul_375_; lean_object* v___x_338__overap_376_; lean_object* v___x_377_; lean_object* v_val_378_; lean_object* v_inv_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_393_; 
v_toCommRing_359_ = lean_ctor_get(v_inst_354_, 0);
lean_inc_ref(v_toCommRing_359_);
v_toSemiring_360_ = lean_ctor_get(v_toCommRing_359_, 0);
lean_inc_ref(v_toSemiring_360_);
v___x_361_ = lp_mathlib_Field_toSemifield___redArg(v_inst_354_);
lean_dec_ref(v_inst_354_);
v_toCommSemiring_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_toCommSemiring_362_);
lean_dec_ref(v___x_361_);
lean_inc(v_N_353_);
v___x_363_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_363_, 0, v_N_353_);
v___x_335__overap_364_ = lp_GRH_New_diagGL___redArg(v___x_363_, v_toCommRing_359_);
v___x_365_ = lean_apply_1(v___x_335__overap_364_, v_t_355_);
v_val_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_val_366_);
v_inv_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_inv_367_);
lean_dec_ref(v___x_365_);
v_val_368_ = lean_ctor_get(v_k_358_, 0);
lean_inc(v_val_368_);
v_inv_369_ = lean_ctor_get(v_k_358_, 1);
lean_inc(v_inv_369_);
v_val_370_ = lean_ctor_get(v_g_356_, 0);
lean_inc(v_val_370_);
v_inv_371_ = lean_ctor_get(v_g_356_, 1);
lean_inc(v_inv_371_);
lean_dec_ref(v_g_356_);
v___x_372_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toCommSemiring_362_);
lean_dec_ref(v_toCommSemiring_362_);
v_toAddCommMonoid_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc_ref(v_toAddCommMonoid_373_);
v___x_374_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_372_);
v_toMul_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_toMul_375_);
lean_dec_ref(v___x_374_);
v___x_338__overap_376_ = lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(v_00_u03c3_357_);
v___x_377_ = lean_apply_1(v___x_338__overap_376_, v_k_358_);
v_val_378_ = lean_ctor_get(v___x_377_, 0);
v_inv_379_ = lean_ctor_get(v___x_377_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_393_ == 0)
{
v___x_381_ = v___x_377_;
v_isShared_382_ = v_isSharedCheck_393_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_inv_379_);
lean_inc(v_val_378_);
lean_dec(v___x_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_393_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v_toAddCommMonoid_384_; lean_object* v___x_385_; lean_object* v_toMul_386_; lean_object* v___x_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___x_391_; 
v___x_383_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_360_);
lean_dec_ref(v_toSemiring_360_);
v_toAddCommMonoid_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref_n(v_toAddCommMonoid_384_, 2);
v___x_385_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_383_);
v_toMul_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_n(v_toMul_386_, 2);
lean_dec_ref(v___x_385_);
v___x_387_ = l_List_finRange(v_N_353_);
lean_inc_ref(v_toAddCommMonoid_373_);
lean_inc(v_toMul_375_);
lean_inc(v___x_387_);
v___f_388_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6___boxed), 11, 9);
lean_closure_set(v___f_388_, 0, v_val_378_);
lean_closure_set(v___f_388_, 1, v_inv_369_);
lean_closure_set(v___f_388_, 2, v_val_370_);
lean_closure_set(v___f_388_, 3, v___x_387_);
lean_closure_set(v___f_388_, 4, v_toMul_375_);
lean_closure_set(v___f_388_, 5, v_toAddCommMonoid_373_);
lean_closure_set(v___f_388_, 6, v_inv_367_);
lean_closure_set(v___f_388_, 7, v_toMul_386_);
lean_closure_set(v___f_388_, 8, v_toAddCommMonoid_384_);
v___f_389_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_389_, 0, v_val_366_);
lean_closure_set(v___f_389_, 1, v_inv_379_);
lean_closure_set(v___f_389_, 2, v_val_368_);
lean_closure_set(v___f_389_, 3, v_inv_371_);
lean_closure_set(v___f_389_, 4, v___x_387_);
lean_closure_set(v___f_389_, 5, v_toMul_375_);
lean_closure_set(v___f_389_, 6, v_toAddCommMonoid_373_);
lean_closure_set(v___f_389_, 7, v_toMul_386_);
lean_closure_set(v___f_389_, 8, v_toAddCommMonoid_384_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___f_389_);
lean_ctor_set(v___x_381_, 0, v___f_388_);
v___x_391_ = v___x_381_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___f_388_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___f_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj(lean_object* v_F_394_, lean_object* v_N_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_t_398_, lean_object* v_g_399_, lean_object* v_00_u03c3_400_, lean_object* v_k_401_){
_start:
{
lean_object* v_toCommRing_402_; lean_object* v_toSemiring_403_; lean_object* v___x_404_; lean_object* v_toCommSemiring_405_; lean_object* v___x_406_; lean_object* v___x_365__overap_407_; lean_object* v___x_408_; lean_object* v_val_409_; lean_object* v_inv_410_; lean_object* v_val_411_; lean_object* v_inv_412_; lean_object* v_val_413_; lean_object* v_inv_414_; lean_object* v___x_415_; lean_object* v_toAddCommMonoid_416_; lean_object* v___x_417_; lean_object* v_toMul_418_; lean_object* v___x_368__overap_419_; lean_object* v___x_420_; lean_object* v_val_421_; lean_object* v_inv_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_436_; 
v_toCommRing_402_ = lean_ctor_get(v_inst_396_, 0);
lean_inc_ref(v_toCommRing_402_);
v_toSemiring_403_ = lean_ctor_get(v_toCommRing_402_, 0);
lean_inc_ref(v_toSemiring_403_);
v___x_404_ = lp_mathlib_Field_toSemifield___redArg(v_inst_396_);
lean_dec_ref(v_inst_396_);
v_toCommSemiring_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc_ref(v_toCommSemiring_405_);
lean_dec_ref(v___x_404_);
lean_inc(v_N_395_);
v___x_406_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_406_, 0, v_N_395_);
v___x_365__overap_407_ = lp_GRH_New_diagGL___redArg(v___x_406_, v_toCommRing_402_);
v___x_408_ = lean_apply_1(v___x_365__overap_407_, v_t_398_);
v_val_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_409_);
v_inv_410_ = lean_ctor_get(v___x_408_, 1);
lean_inc(v_inv_410_);
lean_dec_ref(v___x_408_);
v_val_411_ = lean_ctor_get(v_k_401_, 0);
lean_inc(v_val_411_);
v_inv_412_ = lean_ctor_get(v_k_401_, 1);
lean_inc(v_inv_412_);
v_val_413_ = lean_ctor_get(v_g_399_, 0);
lean_inc(v_val_413_);
v_inv_414_ = lean_ctor_get(v_g_399_, 1);
lean_inc(v_inv_414_);
lean_dec_ref(v_g_399_);
v___x_415_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toCommSemiring_405_);
lean_dec_ref(v_toCommSemiring_405_);
v_toAddCommMonoid_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_toAddCommMonoid_416_);
v___x_417_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_415_);
v_toMul_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_toMul_418_);
lean_dec_ref(v___x_417_);
v___x_368__overap_419_ = lp_mathlib_Matrix_GeneralLinearGroup_map___redArg(v_00_u03c3_400_);
v___x_420_ = lean_apply_1(v___x_368__overap_419_, v_k_401_);
v_val_421_ = lean_ctor_get(v___x_420_, 0);
v_inv_422_ = lean_ctor_get(v___x_420_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_436_ == 0)
{
v___x_424_ = v___x_420_;
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_inv_422_);
lean_inc(v_val_421_);
lean_dec(v___x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_436_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v_toAddCommMonoid_427_; lean_object* v___x_428_; lean_object* v_toMul_429_; lean_object* v___x_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___x_434_; 
v___x_426_ = lp_mathlib_Semiring_toNonUnitalSemiring___redArg(v_toSemiring_403_);
lean_dec_ref(v_toSemiring_403_);
v_toAddCommMonoid_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref_n(v_toAddCommMonoid_427_, 2);
v___x_428_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_426_);
v_toMul_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_toMul_429_, 2);
lean_dec_ref(v___x_428_);
v___x_430_ = l_List_finRange(v_N_395_);
lean_inc_ref(v_toAddCommMonoid_416_);
lean_inc(v_toMul_418_);
lean_inc(v___x_430_);
v___f_431_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__6___boxed), 11, 9);
lean_closure_set(v___f_431_, 0, v_val_421_);
lean_closure_set(v___f_431_, 1, v_inv_412_);
lean_closure_set(v___f_431_, 2, v_val_413_);
lean_closure_set(v___f_431_, 3, v___x_430_);
lean_closure_set(v___f_431_, 4, v_toMul_418_);
lean_closure_set(v___f_431_, 5, v_toAddCommMonoid_416_);
lean_closure_set(v___f_431_, 6, v_inv_410_);
lean_closure_set(v___f_431_, 7, v_toMul_429_);
lean_closure_set(v___f_431_, 8, v_toAddCommMonoid_427_);
v___f_432_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_432_, 0, v_val_409_);
lean_closure_set(v___f_432_, 1, v_inv_422_);
lean_closure_set(v___f_432_, 2, v_val_411_);
lean_closure_set(v___f_432_, 3, v_inv_414_);
lean_closure_set(v___f_432_, 4, v___x_430_);
lean_closure_set(v___f_432_, 5, v_toMul_418_);
lean_closure_set(v___f_432_, 6, v_toAddCommMonoid_416_);
lean_closure_set(v___f_432_, 7, v_toMul_429_);
lean_closure_set(v___f_432_, 8, v_toAddCommMonoid_427_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___f_432_);
lean_ctor_set(v___x_424_, 0, v___f_431_);
v___x_434_ = v___x_424_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___f_431_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___f_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj___boxed(lean_object* v_F_437_, lean_object* v_N_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_t_441_, lean_object* v_g_442_, lean_object* v_00_u03c3_443_, lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = lp_GRH___private_Lib_LocalGL_Iwahori_ParahoricStructure_0__New_twistedConj(v_F_437_, v_N_438_, v_inst_439_, v_inst_440_, v_t_441_, v_g_442_, v_00_u03c3_443_, v_k_444_);
lean_dec_ref(v_inst_440_);
return v_res_445_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Hecke_ClassSums(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_LocalGL_Iwahori_ParahoricStructure(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Hecke_ClassSums(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_LinearAlgebra_HermiteForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
