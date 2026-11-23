// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.LevGSym
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
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
lean_object* lp_tree_Formalism_L2_Col_chiSym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_refl(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_reindex___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Units_mapEquiv___redArg(lean_object*);
lean_object* lp_mathlib_MonoidHom_submonoidComap___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_lamPar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_zero___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_mathlib_Units_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_Ring_toAddCommGroup___redArg(lean_object*);
lean_object* lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_transvection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_inclusion___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdxInv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdxInv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_symPerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_symPerm___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsymF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsymF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_Col_lamXmsym___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_inclusion___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_Col_lamXmsym___redArg___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_Col_lamXmsym___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_elemGL___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_elemGL(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdx(lean_object* v_k_1_, lean_object* v_rS_2_, lean_object* v_i_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_i_3_, v_k_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_nat_add(v_k_1_, v_rS_2_);
v___x_6_ = lean_nat_dec_lt(v_i_3_, v___x_5_);
lean_dec(v___x_5_);
if (v___x_6_ == 0)
{
lean_inc(v_i_3_);
return v_i_3_;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = lean_nat_sub(v_i_3_, v_k_1_);
return v___x_7_;
}
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_add(v_i_3_, v_rS_2_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdx___boxed(lean_object* v_k_9_, lean_object* v_rS_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_tree_Formalism_L2_Col_symIdx(v_k_9_, v_rS_10_, v_i_11_);
lean_dec(v_i_11_);
lean_dec(v_rS_10_);
lean_dec(v_k_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdxInv(lean_object* v_k_13_, lean_object* v_rS_14_, lean_object* v_i_15_){
_start:
{
uint8_t v___x_16_; 
v___x_16_ = lean_nat_dec_lt(v_i_15_, v_rS_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_nat_add(v_rS_14_, v_k_13_);
v___x_18_ = lean_nat_dec_lt(v_i_15_, v___x_17_);
lean_dec(v___x_17_);
if (v___x_18_ == 0)
{
lean_inc(v_i_15_);
return v_i_15_;
}
else
{
lean_object* v___x_19_; 
v___x_19_ = lean_nat_sub(v_i_15_, v_rS_14_);
return v___x_19_;
}
}
else
{
lean_object* v___x_20_; 
v___x_20_ = lean_nat_add(v_i_15_, v_k_13_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symIdxInv___boxed(lean_object* v_k_21_, lean_object* v_rS_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_tree_Formalism_L2_Col_symIdxInv(v_k_21_, v_rS_22_, v_i_23_);
lean_dec(v_i_23_);
lean_dec(v_rS_22_);
lean_dec(v_k_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__0(lean_object* v_k_25_, lean_object* v_rS_26_, lean_object* v_i_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_tree_Formalism_L2_Col_symIdx(v_k_25_, v_rS_26_, v_i_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__0___boxed(lean_object* v_k_29_, lean_object* v_rS_30_, lean_object* v_i_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_tree_Formalism_L2_Col_symPerm___lam__0(v_k_29_, v_rS_30_, v_i_31_);
lean_dec(v_i_31_);
lean_dec(v_rS_30_);
lean_dec(v_k_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__1(lean_object* v_k_33_, lean_object* v_rS_34_, lean_object* v_i_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_tree_Formalism_L2_Col_symIdxInv(v_k_33_, v_rS_34_, v_i_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___lam__1___boxed(lean_object* v_k_37_, lean_object* v_rS_38_, lean_object* v_i_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_L2_Col_symPerm___lam__1(v_k_37_, v_rS_38_, v_i_39_);
lean_dec(v_i_39_);
lean_dec(v_rS_38_);
lean_dec(v_k_37_);
return v_res_40_;
}
}
static lean_object* _init_lp_tree_Formalism_L2_Col_symPerm___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm(lean_object* v_n_42_, lean_object* v_k_43_, lean_object* v_rS_44_){
_start:
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = lean_nat_add(v_k_43_, v_rS_44_);
v___x_46_ = lean_nat_dec_le(v___x_45_, v_n_42_);
lean_dec(v___x_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; 
lean_dec(v_rS_44_);
lean_dec(v_k_43_);
v___x_47_ = lean_obj_once(&lp_tree_Formalism_L2_Col_symPerm___closed__0, &lp_tree_Formalism_L2_Col_symPerm___closed__0_once, _init_lp_tree_Formalism_L2_Col_symPerm___closed__0);
return v___x_47_;
}
else
{
lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___x_50_; 
lean_inc(v_rS_44_);
lean_inc(v_k_43_);
v___f_48_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_symPerm___lam__0___boxed), 3, 2);
lean_closure_set(v___f_48_, 0, v_k_43_);
lean_closure_set(v___f_48_, 1, v_rS_44_);
v___f_49_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_symPerm___lam__1___boxed), 3, 2);
lean_closure_set(v___f_49_, 0, v_k_43_);
lean_closure_set(v___f_49_, 1, v_rS_44_);
v___x_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_50_, 0, v___f_48_);
lean_ctor_set(v___x_50_, 1, v___f_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_symPerm___boxed(lean_object* v_n_51_, lean_object* v_k_52_, lean_object* v_rS_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_L2_Col_symPerm(v_n_51_, v_k_52_, v_rS_53_);
lean_dec(v_n_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___redArg(lean_object* v_n_55_, lean_object* v_k_56_, lean_object* v_rS_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_toFun_61_; 
v___x_58_ = lp_tree_Formalism_L2_Col_symPerm(v_n_55_, v_k_56_, v_rS_57_);
lean_inc_ref(v___x_58_);
v___x_59_ = lp_mathlib_Matrix_reindex___redArg(v___x_58_, v___x_58_);
v___x_60_ = lp_mathlib_Units_mapEquiv___redArg(v___x_59_);
v_toFun_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_toFun_61_);
lean_dec_ref(v___x_60_);
return v_toFun_61_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___redArg___boxed(lean_object* v_n_62_, lean_object* v_k_63_, lean_object* v_rS_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lp_tree_Formalism_L2_Col_toSymOrd___redArg(v_n_62_, v_k_63_, v_rS_64_);
lean_dec(v_n_62_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd(lean_object* v_00_u03ba_66_, lean_object* v_inst_67_, lean_object* v_n_68_, lean_object* v_k_69_, lean_object* v_rS_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_tree_Formalism_L2_Col_toSymOrd___redArg(v_n_68_, v_k_69_, v_rS_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_toSymOrd___boxed(lean_object* v_00_u03ba_72_, lean_object* v_inst_73_, lean_object* v_n_74_, lean_object* v_k_75_, lean_object* v_rS_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lp_tree_Formalism_L2_Col_toSymOrd(v_00_u03ba_72_, v_inst_73_, v_n_74_, v_k_75_, v_rS_76_);
lean_dec(v_n_74_);
lean_dec_ref(v_inst_73_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsymF(lean_object* v_00_u03ba_78_, lean_object* v_inst_79_, lean_object* v_n_80_, lean_object* v_k_81_, lean_object* v_rS_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HPsymF___boxed(lean_object* v_00_u03ba_84_, lean_object* v_inst_85_, lean_object* v_n_86_, lean_object* v_k_87_, lean_object* v_rS_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lp_tree_Formalism_L2_Col_HPsymF(v_00_u03ba_84_, v_inst_85_, v_n_86_, v_k_87_, v_rS_88_);
lean_dec(v_rS_88_);
lean_dec(v_k_87_);
lean_dec(v_n_86_);
lean_dec_ref(v_inst_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_00_u03c8_92_, lean_object* v_n_93_, lean_object* v_k_94_, lean_object* v_rS_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___f_99_; 
lean_inc(v_rS_95_);
lean_inc(v_k_94_);
lean_inc(v_n_93_);
v___x_96_ = lp_tree_Formalism_L2_Col_chiSym___redArg(v_inst_90_, v_inst_91_, v_00_u03c8_92_, v_n_93_, v_k_94_, v_rS_95_);
v___x_97_ = lp_tree_Formalism_L2_Col_toSymOrd___redArg(v_n_93_, v_k_94_, v_rS_95_);
lean_dec(v_n_93_);
v___f_98_ = lean_alloc_closure((void*)(lp_mathlib_MonoidHom_submonoidComap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_98_, 0, v___x_97_);
v___f_99_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_99_, 0, v___f_98_);
lean_closure_set(v___f_99_, 1, v___x_96_);
return v___f_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___redArg___boxed(lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_00_u03c8_102_, lean_object* v_n_103_, lean_object* v_k_104_, lean_object* v_rS_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_tree_Formalism_L2_Col_chiSymF___redArg(v_inst_100_, v_inst_101_, v_00_u03c8_102_, v_n_103_, v_k_104_, v_rS_105_);
lean_dec_ref(v_inst_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF(lean_object* v_00_u03ba_107_, lean_object* v_inst_108_, lean_object* v_K_109_, lean_object* v_inst_110_, lean_object* v_00_u03c8_111_, lean_object* v_n_112_, lean_object* v_k_113_, lean_object* v_rS_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lp_tree_Formalism_L2_Col_chiSymF___redArg(v_inst_108_, v_inst_110_, v_00_u03c8_111_, v_n_112_, v_k_113_, v_rS_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_chiSymF___boxed(lean_object* v_00_u03ba_116_, lean_object* v_inst_117_, lean_object* v_K_118_, lean_object* v_inst_119_, lean_object* v_00_u03c8_120_, lean_object* v_n_121_, lean_object* v_k_122_, lean_object* v_rS_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_tree_Formalism_L2_Col_chiSymF(v_00_u03ba_116_, v_inst_117_, v_K_118_, v_inst_119_, v_00_u03c8_120_, v_n_121_, v_k_122_, v_rS_123_);
lean_dec_ref(v_inst_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsym(lean_object* v_00_u03ba_125_, lean_object* v_inst_126_, lean_object* v_n_127_, lean_object* v_k_128_, lean_object* v_r_129_, lean_object* v_t_130_, lean_object* v_j_131_, lean_object* v_rS_132_, lean_object* v_h_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HJsym___boxed(lean_object* v_00_u03ba_135_, lean_object* v_inst_136_, lean_object* v_n_137_, lean_object* v_k_138_, lean_object* v_r_139_, lean_object* v_t_140_, lean_object* v_j_141_, lean_object* v_rS_142_, lean_object* v_h_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_tree_Formalism_L2_Col_HJsym(v_00_u03ba_135_, v_inst_136_, v_n_137_, v_k_138_, v_r_139_, v_t_140_, v_j_141_, v_rS_142_, v_h_143_);
lean_dec(v_rS_142_);
lean_dec(v_j_141_);
lean_dec(v_t_140_);
lean_dec(v_r_139_);
lean_dec(v_k_138_);
lean_dec(v_n_137_);
lean_dec_ref(v_inst_136_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_00_u03c8_147_, lean_object* v_00_u03c7_148_, lean_object* v_n_149_, lean_object* v_k_150_, lean_object* v_r_151_, lean_object* v_t_152_, lean_object* v_j_153_, lean_object* v_rS_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = l_List_replicateTR___redArg(v_j_153_, v_t_152_);
lean_inc(v_r_151_);
lean_inc_ref(v_inst_145_);
v___x_156_ = lp_tree_Formalism_L2_Col_chiSymF___redArg(v_inst_145_, v_inst_146_, v_00_u03c8_147_, v_r_151_, v_k_150_, v_rS_154_);
v___x_157_ = lp_tree_Formalism_L2_Col_lamPar___redArg(v_n_149_, v_inst_145_, v_inst_146_, v_r_151_, v___x_155_, v___x_156_, v_00_u03c7_148_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___redArg___boxed(lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_00_u03c8_160_, lean_object* v_00_u03c7_161_, lean_object* v_n_162_, lean_object* v_k_163_, lean_object* v_r_164_, lean_object* v_t_165_, lean_object* v_j_166_, lean_object* v_rS_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = lp_tree_Formalism_L2_Col_lamJsym___redArg(v_inst_158_, v_inst_159_, v_00_u03c8_160_, v_00_u03c7_161_, v_n_162_, v_k_163_, v_r_164_, v_t_165_, v_j_166_, v_rS_167_);
lean_dec_ref(v_inst_159_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym(lean_object* v_00_u03ba_169_, lean_object* v_inst_170_, lean_object* v_K_171_, lean_object* v_inst_172_, lean_object* v_00_u03c8_173_, lean_object* v_00_u03c7_174_, lean_object* v_n_175_, lean_object* v_k_176_, lean_object* v_r_177_, lean_object* v_t_178_, lean_object* v_j_179_, lean_object* v_rS_180_, lean_object* v_h_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lp_tree_Formalism_L2_Col_lamJsym___redArg(v_inst_170_, v_inst_172_, v_00_u03c8_173_, v_00_u03c7_174_, v_n_175_, v_k_176_, v_r_177_, v_t_178_, v_j_179_, v_rS_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamJsym___boxed(lean_object* v_00_u03ba_183_, lean_object* v_inst_184_, lean_object* v_K_185_, lean_object* v_inst_186_, lean_object* v_00_u03c8_187_, lean_object* v_00_u03c7_188_, lean_object* v_n_189_, lean_object* v_k_190_, lean_object* v_r_191_, lean_object* v_t_192_, lean_object* v_j_193_, lean_object* v_rS_194_, lean_object* v_h_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_tree_Formalism_L2_Col_lamJsym(v_00_u03ba_183_, v_inst_184_, v_K_185_, v_inst_186_, v_00_u03c8_187_, v_00_u03c7_188_, v_n_189_, v_k_190_, v_r_191_, v_t_192_, v_j_193_, v_rS_194_, v_h_195_);
lean_dec_ref(v_inst_186_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsym(lean_object* v_00_u03ba_197_, lean_object* v_inst_198_, lean_object* v_n_199_, lean_object* v_k_200_, lean_object* v_r_201_, lean_object* v_t_202_, lean_object* v_m_203_, lean_object* v_rS_204_, lean_object* v_h_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_HXmsym___boxed(lean_object* v_00_u03ba_207_, lean_object* v_inst_208_, lean_object* v_n_209_, lean_object* v_k_210_, lean_object* v_r_211_, lean_object* v_t_212_, lean_object* v_m_213_, lean_object* v_rS_214_, lean_object* v_h_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_tree_Formalism_L2_Col_HXmsym(v_00_u03ba_207_, v_inst_208_, v_n_209_, v_k_210_, v_r_211_, v_t_212_, v_m_213_, v_rS_214_, v_h_215_);
lean_dec(v_rS_214_);
lean_dec(v_m_213_);
lean_dec(v_t_212_);
lean_dec(v_r_211_);
lean_dec(v_k_210_);
lean_dec(v_n_209_);
lean_dec_ref(v_inst_208_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___redArg(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_00_u03c8_220_, lean_object* v_00_u03c7_221_, lean_object* v_n_222_, lean_object* v_k_223_, lean_object* v_r_224_, lean_object* v_t_225_, lean_object* v_m_226_, lean_object* v_rS_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___f_229_; lean_object* v___f_230_; 
v___x_228_ = lp_tree_Formalism_L2_Col_lamJsym___redArg(v_inst_218_, v_inst_219_, v_00_u03c8_220_, v_00_u03c7_221_, v_n_222_, v_k_223_, v_r_224_, v_t_225_, v_m_226_, v_rS_227_);
v___f_229_ = ((lean_object*)(lp_tree_Formalism_L2_Col_lamXmsym___redArg___closed__0));
v___f_230_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_230_, 0, v___f_229_);
lean_closure_set(v___f_230_, 1, v___x_228_);
return v___f_230_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___redArg___boxed(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_00_u03c8_233_, lean_object* v_00_u03c7_234_, lean_object* v_n_235_, lean_object* v_k_236_, lean_object* v_r_237_, lean_object* v_t_238_, lean_object* v_m_239_, lean_object* v_rS_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = lp_tree_Formalism_L2_Col_lamXmsym___redArg(v_inst_231_, v_inst_232_, v_00_u03c8_233_, v_00_u03c7_234_, v_n_235_, v_k_236_, v_r_237_, v_t_238_, v_m_239_, v_rS_240_);
lean_dec_ref(v_inst_232_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym(lean_object* v_00_u03ba_242_, lean_object* v_inst_243_, lean_object* v_K_244_, lean_object* v_inst_245_, lean_object* v_00_u03c8_246_, lean_object* v_00_u03c7_247_, lean_object* v_n_248_, lean_object* v_k_249_, lean_object* v_r_250_, lean_object* v_t_251_, lean_object* v_m_252_, lean_object* v_rS_253_, lean_object* v_h_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lp_tree_Formalism_L2_Col_lamXmsym___redArg(v_inst_243_, v_inst_245_, v_00_u03c8_246_, v_00_u03c7_247_, v_n_248_, v_k_249_, v_r_250_, v_t_251_, v_m_252_, v_rS_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_lamXmsym___boxed(lean_object* v_00_u03ba_256_, lean_object* v_inst_257_, lean_object* v_K_258_, lean_object* v_inst_259_, lean_object* v_00_u03c8_260_, lean_object* v_00_u03c7_261_, lean_object* v_n_262_, lean_object* v_k_263_, lean_object* v_r_264_, lean_object* v_t_265_, lean_object* v_m_266_, lean_object* v_rS_267_, lean_object* v_h_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_tree_Formalism_L2_Col_lamXmsym(v_00_u03ba_256_, v_inst_257_, v_K_258_, v_inst_259_, v_00_u03c8_260_, v_00_u03c7_261_, v_n_262_, v_k_263_, v_r_264_, v_t_265_, v_m_266_, v_rS_267_, v_h_268_);
lean_dec_ref(v_inst_259_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0(lean_object* v_k_270_, lean_object* v_c_271_, lean_object* v_a_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_lt(v_a_272_, v_k_270_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = lean_nat_add(v_k_270_, v_c_271_);
v___x_275_ = lean_nat_dec_lt(v_a_272_, v___x_274_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_nat_sub(v_a_272_, v_c_271_);
lean_dec(v_a_272_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_nat_sub(v_a_272_, v_k_270_);
lean_dec(v_a_272_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_a_272_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0___boxed(lean_object* v_k_281_, lean_object* v_c_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0(v_k_281_, v_c_282_, v_a_283_);
lean_dec(v_c_282_);
lean_dec(v_k_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1(lean_object* v_k_285_, lean_object* v_c_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v_val_288_; uint8_t v___x_289_; 
v_val_288_ = lean_ctor_get(v_x_287_, 0);
v___x_289_ = lean_nat_dec_lt(v_val_288_, v_k_285_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; 
v___x_290_ = lean_nat_add(v_val_288_, v_c_286_);
return v___x_290_;
}
else
{
lean_inc(v_val_288_);
return v_val_288_;
}
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; 
v_val_291_ = lean_ctor_get(v_x_287_, 0);
v___x_292_ = lean_nat_add(v_k_285_, v_val_291_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1___boxed(lean_object* v_k_293_, lean_object* v_c_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1(v_k_293_, v_c_294_, v_x_295_);
lean_dec_ref(v_x_295_);
lean_dec(v_c_294_);
lean_dec(v_k_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___redArg(lean_object* v_c_297_, lean_object* v_k_298_){
_start:
{
lean_object* v___f_299_; lean_object* v___f_300_; lean_object* v___x_301_; 
lean_inc(v_c_297_);
lean_inc(v_k_298_);
v___f_299_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_299_, 0, v_k_298_);
lean_closure_set(v___f_299_, 1, v_c_297_);
v___f_300_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_insEquiv___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_300_, 0, v_k_298_);
lean_closure_set(v___f_300_, 1, v_c_297_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___f_299_);
lean_ctor_set(v___x_301_, 1, v___f_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv(lean_object* v_N_302_, lean_object* v_c_303_, lean_object* v_k_304_, lean_object* v_N_x27_305_, lean_object* v_hk_306_, lean_object* v_hN_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lp_tree_Formalism_L2_Col_insEquiv___redArg(v_c_303_, v_k_304_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insEquiv___boxed(lean_object* v_N_309_, lean_object* v_c_310_, lean_object* v_k_311_, lean_object* v_N_x27_312_, lean_object* v_hk_313_, lean_object* v_hN_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = lp_tree_Formalism_L2_Col_insEquiv(v_N_309_, v_c_310_, v_k_311_, v_N_x27_312_, v_hk_313_, v_hN_314_);
lean_dec(v_N_x27_312_);
lean_dec(v_N_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0(lean_object* v_toOne_316_, lean_object* v_x_317_){
_start:
{
lean_inc(v_toOne_316_);
return v_toOne_316_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0___boxed(lean_object* v_toOne_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0(v_toOne_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec(v_toOne_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__1(lean_object* v_toZero_321_, lean_object* v_c_322_, lean_object* v___f_323_, lean_object* v_A_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_inc(v_toZero_321_);
v___x_327_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_zero___aux__1___boxed), 6, 4);
lean_closure_set(v___x_327_, 0, lean_box(0));
lean_closure_set(v___x_327_, 1, lean_box(0));
lean_closure_set(v___x_327_, 2, lean_box(0));
lean_closure_set(v___x_327_, 3, v_toZero_321_);
v___x_328_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_328_, 0, v_c_322_);
v___x_329_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_diagonal), 7, 5);
lean_closure_set(v___x_329_, 0, lean_box(0));
lean_closure_set(v___x_329_, 1, lean_box(0));
lean_closure_set(v___x_329_, 2, v___x_328_);
lean_closure_set(v___x_329_, 3, v_toZero_321_);
lean_closure_set(v___x_329_, 4, v___f_323_);
lean_inc_ref(v___x_327_);
v___x_330_ = lp_mathlib_Matrix_fromBlocks___redArg(v_A_324_, v___x_327_, v___x_327_, v___x_329_, v___y_325_, v___y_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___redArg(lean_object* v_inst_331_, lean_object* v_c_332_){
_start:
{
lean_object* v_toSemiring_333_; lean_object* v___x_334_; lean_object* v_toZero_335_; lean_object* v___x_336_; lean_object* v_toAddMonoidWithOne_337_; lean_object* v_toOne_338_; lean_object* v___f_339_; lean_object* v___f_340_; 
v_toSemiring_333_ = lean_ctor_get(v_inst_331_, 0);
lean_inc_ref(v_toSemiring_333_);
v___x_334_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_333_);
v_toZero_335_ = lean_ctor_get(v___x_334_, 1);
lean_inc(v_toZero_335_);
lean_dec_ref(v___x_334_);
v___x_336_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_inst_331_);
v_toAddMonoidWithOne_337_ = lean_ctor_get(v___x_336_, 1);
lean_inc_ref(v_toAddMonoidWithOne_337_);
lean_dec_ref(v___x_336_);
v_toOne_338_ = lean_ctor_get(v_toAddMonoidWithOne_337_, 2);
lean_inc(v_toOne_338_);
lean_dec_ref(v_toAddMonoidWithOne_337_);
v___f_339_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_339_, 0, v_toOne_338_);
v___f_340_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_blkOneHom___redArg___lam__1), 6, 3);
lean_closure_set(v___f_340_, 0, v_toZero_335_);
lean_closure_set(v___f_340_, 1, v_c_332_);
lean_closure_set(v___f_340_, 2, v___f_339_);
return v___f_340_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom(lean_object* v_00_u03ba_341_, lean_object* v_inst_342_, lean_object* v_N_343_, lean_object* v_c_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lp_tree_Formalism_L2_Col_blkOneHom___redArg(v_inst_342_, v_c_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_blkOneHom___boxed(lean_object* v_00_u03ba_346_, lean_object* v_inst_347_, lean_object* v_N_348_, lean_object* v_c_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = lp_tree_Formalism_L2_Col_blkOneHom(v_00_u03ba_346_, v_inst_347_, v_N_348_, v_c_349_);
lean_dec(v_N_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL___redArg(lean_object* v_inst_351_, lean_object* v_c_352_, lean_object* v_k_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_toFun_357_; lean_object* v___x_358_; lean_object* v___f_359_; lean_object* v___f_360_; 
lean_inc(v_c_352_);
v___x_354_ = lp_tree_Formalism_L2_Col_insEquiv___redArg(v_c_352_, v_k_353_);
v___x_355_ = lp_mathlib_Equiv_symm___redArg(v___x_354_);
lean_inc_ref(v___x_355_);
v___x_356_ = lp_mathlib_Matrix_reindex___redArg(v___x_355_, v___x_355_);
v_toFun_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_toFun_357_);
lean_dec_ref(v___x_356_);
v___x_358_ = lp_tree_Formalism_L2_Col_blkOneHom___redArg(v_inst_351_, v_c_352_);
v___f_359_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_359_, 0, v___x_358_);
lean_closure_set(v___f_359_, 1, v_toFun_357_);
v___f_360_ = lean_alloc_closure((void*)(lp_mathlib_Units_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_360_, 0, v___f_359_);
return v___f_360_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL(lean_object* v_00_u03ba_361_, lean_object* v_inst_362_, lean_object* v_N_363_, lean_object* v_c_364_, lean_object* v_k_365_, lean_object* v_N_x27_366_, lean_object* v_hk_367_, lean_object* v_hN_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lp_tree_Formalism_L2_Col_insGL___redArg(v_inst_362_, v_c_364_, v_k_365_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_insGL___boxed(lean_object* v_00_u03ba_370_, lean_object* v_inst_371_, lean_object* v_N_372_, lean_object* v_c_373_, lean_object* v_k_374_, lean_object* v_N_x27_375_, lean_object* v_hk_376_, lean_object* v_hN_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = lp_tree_Formalism_L2_Col_insGL(v_00_u03ba_370_, v_inst_371_, v_N_372_, v_c_373_, v_k_374_, v_N_x27_375_, v_hk_376_, v_hN_377_);
lean_dec(v_N_x27_375_);
lean_dec(v_N_372_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_elemGL___redArg(lean_object* v_inst_379_, lean_object* v_n_380_, lean_object* v_i_381_, lean_object* v_j_382_, lean_object* v_c_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_toNeg_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v___x_384_ = lp_mathlib_Ring_toAddCommGroup___redArg(v_inst_379_);
v___x_385_ = lp_mathlib_SubNegZeroMonoid_toNegZeroClass___redArg(v___x_384_);
lean_dec_ref(v___x_384_);
v_toNeg_386_ = lean_ctor_get(v___x_385_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_385_, 0);
lean_dec(v_unused_398_);
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_toNeg_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_390_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_390_, 0, v_n_380_);
lean_inc(v_c_383_);
lean_inc(v_j_382_);
lean_inc(v_i_381_);
lean_inc_ref(v_inst_379_);
lean_inc_ref(v___x_390_);
v___x_391_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transvection), 9, 7);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, lean_box(0));
lean_closure_set(v___x_391_, 2, v___x_390_);
lean_closure_set(v___x_391_, 3, v_inst_379_);
lean_closure_set(v___x_391_, 4, v_i_381_);
lean_closure_set(v___x_391_, 5, v_j_382_);
lean_closure_set(v___x_391_, 6, v_c_383_);
v___x_392_ = lean_apply_1(v_toNeg_386_, v_c_383_);
v___x_393_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transvection), 9, 7);
lean_closure_set(v___x_393_, 0, lean_box(0));
lean_closure_set(v___x_393_, 1, lean_box(0));
lean_closure_set(v___x_393_, 2, v___x_390_);
lean_closure_set(v___x_393_, 3, v_inst_379_);
lean_closure_set(v___x_393_, 4, v_i_381_);
lean_closure_set(v___x_393_, 5, v_j_382_);
lean_closure_set(v___x_393_, 6, v___x_392_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_393_);
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_395_ = v___x_388_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_elemGL(lean_object* v_00_u03ba_399_, lean_object* v_inst_400_, lean_object* v_n_401_, lean_object* v_i_402_, lean_object* v_j_403_, lean_object* v_hij_404_, lean_object* v_c_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lp_tree_Formalism_L2_Col_elemGL___redArg(v_inst_400_, v_n_401_, v_i_402_, v_j_403_, v_c_405_);
return v___x_406_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_LevGSym(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
