// Lean compiler output
// Module: Lib.Cohomology.Etale.RelativeChains
// Imports: public import Init public meta import Init public import Lib.Cohomology.Etale.DenseSubfunctors public import Lib.Cohomology.Hodge.CupProduct
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
lean_object* lp_mathlib_FreeAbelianGroup_of___redArg(lean_object*);
lean_object* lp_mathlib_TensorProduct_tmul___redArg(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_abTensor___redArg();
lean_object* lp_GRH_New_Variety_abCoker_00_u03c0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_freeAb___redArg();
lean_object* lp_GRH_New_Variety_freeAb_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_AddCommGrpCat_instCategory;
lean_object* lp_GRH_New_Variety_relFreeAb___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_abCoker_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Subfunctor_homOfLe___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_CategoryTheory_typesCartesianMonoidalCategory;
lean_object* lp_mathlib_CategoryTheory_Monoidal_FunctorCategory_tensorObj___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Subfunctor_toFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_freeAb_prod___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_freeAb_prod___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___closed__1;
static const lean_closure_object lp_GRH_New_Variety_freeAb_prod___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_freeAb_prod___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___closed__2 = (const lean_object*)&lp_GRH_New_Variety_freeAb_prod___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_relFreeAb_map___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_abCoker_00_u03c0___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_relFreeAb_map___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_relFreeAb_map___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_relFreeAb_restrict___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_CategoryTheory_Subfunctor_homOfLe___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_relFreeAb_restrict___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_relFreeAb_restrict___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___lam__0(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_fst_3_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_fst_3_);
v_snd_4_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_snd_4_);
lean_dec_ref(v_x_2_);
v___x_5_ = lp_mathlib_FreeAbelianGroup_of___redArg(v_fst_3_);
v___x_6_ = lp_mathlib_FreeAbelianGroup_of___redArg(v_snd_4_);
v___x_7_ = lp_mathlib_TensorProduct_tmul___redArg(v___x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg___lam__0___boxed(lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_GRH_New_Variety_freeAb_prod___redArg___lam__0(v_x_8_, v_x_9_);
lean_dec(v_x_8_);
return v_res_10_;
}
}
static lean_object* _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lp_GRH_New_Variety_abTensor___redArg();
return v___x_11_;
}
}
static lean_object* _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__1(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lp_GRH_New_Variety_freeAb___redArg();
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___redArg(lean_object* v_X_14_, lean_object* v_Y_15_){
_start:
{
lean_object* v___x_16_; lean_object* v_obj_17_; lean_object* v___x_18_; lean_object* v_obj_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_obj_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___f_26_; 
v___x_16_ = lean_obj_once(&lp_GRH_New_Variety_freeAb_prod___redArg___closed__0, &lp_GRH_New_Variety_freeAb_prod___redArg___closed__0_once, _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__0);
v_obj_17_ = lean_ctor_get(v___x_16_, 0);
v___x_18_ = lean_obj_once(&lp_GRH_New_Variety_freeAb_prod___redArg___closed__1, &lp_GRH_New_Variety_freeAb_prod___redArg___closed__1_once, _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__1);
v_obj_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc_n(v_obj_19_, 2);
v___x_20_ = lean_apply_1(v_obj_19_, v_X_14_);
lean_inc(v_obj_17_);
v___x_21_ = lean_apply_1(v_obj_17_, v___x_20_);
v_obj_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_obj_22_);
lean_dec_ref(v___x_21_);
v___f_23_ = ((lean_object*)(lp_GRH_New_Variety_freeAb_prod___redArg___closed__2));
v___x_24_ = lean_apply_1(v_obj_19_, v_Y_15_);
v___x_25_ = lean_apply_1(v_obj_22_, v___x_24_);
v___f_26_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_freeAb_desc___redArg___lam__0), 4, 2);
lean_closure_set(v___f_26_, 0, v___x_25_);
lean_closure_set(v___f_26_, 1, v___f_23_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod(lean_object* v_C_27_, lean_object* v_inst_28_, lean_object* v_X_29_, lean_object* v_Y_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_GRH_New_Variety_freeAb_prod___redArg(v_X_29_, v_Y_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_freeAb_prod___boxed(lean_object* v_C_32_, lean_object* v_inst_33_, lean_object* v_X_34_, lean_object* v_Y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lp_GRH_New_Variety_freeAb_prod(v_C_32_, v_inst_33_, v_X_34_, v_Y_35_);
lean_dec_ref(v_inst_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_GRH_New_Variety_zeroSection___redArg();
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection(lean_object* v_C_41_, lean_object* v_inst_42_, lean_object* v_N_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_zeroSection___boxed(lean_object* v_C_45_, lean_object* v_inst_46_, lean_object* v_N_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_GRH_New_Variety_zeroSection(v_C_45_, v_inst_46_, v_N_47_);
lean_dec_ref(v_N_47_);
lean_dec_ref(v_inst_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___redArg(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___redArg___boxed(lean_object* v___dummy_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lp_GRH_New_Variety_locallyZero___redArg();
return v_res_52_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero(lean_object* v_C_53_, lean_object* v_inst_54_, lean_object* v_F_55_, lean_object* v_N_56_, lean_object* v_A_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_box(0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locallyZero___boxed(lean_object* v_C_59_, lean_object* v_inst_60_, lean_object* v_F_61_, lean_object* v_N_62_, lean_object* v_A_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_GRH_New_Variety_locallyZero(v_C_59_, v_inst_60_, v_F_61_, v_N_62_, v_A_63_);
lean_dec(v_A_63_);
lean_dec_ref(v_N_62_);
lean_dec_ref(v_F_61_);
lean_dec_ref(v_inst_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = lp_GRH_New_Variety_permutedPairs___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs(lean_object* v_C_69_, lean_object* v_inst_70_, lean_object* v_V_71_, lean_object* v_V_x27_72_, lean_object* v_V_x27_x27_73_, lean_object* v_00_u03b9_74_, lean_object* v_f_75_, lean_object* v_p_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_permutedPairs___boxed(lean_object* v_C_78_, lean_object* v_inst_79_, lean_object* v_V_80_, lean_object* v_V_x27_81_, lean_object* v_V_x27_x27_82_, lean_object* v_00_u03b9_83_, lean_object* v_f_84_, lean_object* v_p_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_GRH_New_Variety_permutedPairs(v_C_78_, v_inst_79_, v_V_80_, v_V_x27_81_, v_V_x27_x27_82_, v_00_u03b9_83_, v_f_84_, v_p_85_);
lean_dec(v_p_85_);
lean_dec(v_f_84_);
lean_dec_ref(v_V_x27_x27_82_);
lean_dec_ref(v_V_x27_81_);
lean_dec_ref(v_V_80_);
lean_dec_ref(v_inst_79_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map___redArg(lean_object* v_V_88_, lean_object* v_V_x27_89_, lean_object* v_u_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_obj_93_; lean_object* v_map_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___f_101_; 
v___x_91_ = lp_mathlib_AddCommGrpCat_instCategory;
v___x_92_ = lean_obj_once(&lp_GRH_New_Variety_freeAb_prod___redArg___closed__1, &lp_GRH_New_Variety_freeAb_prod___redArg___closed__1_once, _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__1);
v_obj_93_ = lean_ctor_get(v___x_92_, 0);
v_map_94_ = lean_ctor_get(v___x_92_, 1);
lean_inc_ref_n(v_V_88_, 2);
v___x_95_ = lp_GRH_New_Variety_relFreeAb___redArg(v_V_88_);
lean_inc_n(v_obj_93_, 2);
lean_inc_ref(v_V_x27_89_);
v___x_96_ = lean_apply_1(v_obj_93_, v_V_x27_89_);
v___x_97_ = lean_apply_1(v_obj_93_, v_V_88_);
lean_inc(v_map_94_);
v___x_98_ = lean_apply_3(v_map_94_, v_V_x27_89_, v_V_88_, v_u_90_);
v___f_99_ = ((lean_object*)(lp_GRH_New_Variety_relFreeAb_map___redArg___closed__0));
v___f_100_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0), 7, 6);
lean_closure_set(v___f_100_, 0, v___x_91_);
lean_closure_set(v___f_100_, 1, v___x_96_);
lean_closure_set(v___f_100_, 2, v___x_97_);
lean_closure_set(v___f_100_, 3, v___x_95_);
lean_closure_set(v___f_100_, 4, v___x_98_);
lean_closure_set(v___f_100_, 5, v___f_99_);
v___f_101_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abCoker_desc___redArg___lam__0), 3, 1);
lean_closure_set(v___f_101_, 0, v___f_100_);
return v___f_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map(lean_object* v_C_102_, lean_object* v_inst_103_, lean_object* v_V_104_, lean_object* v_V_x27_105_, lean_object* v_U_106_, lean_object* v_U_x27_107_, lean_object* v_u_108_, lean_object* v_h_x27_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lp_GRH_New_Variety_relFreeAb_map___redArg(v_V_104_, v_V_x27_105_, v_u_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_map___boxed(lean_object* v_C_111_, lean_object* v_inst_112_, lean_object* v_V_113_, lean_object* v_V_x27_114_, lean_object* v_U_115_, lean_object* v_U_x27_116_, lean_object* v_u_117_, lean_object* v_h_x27_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_GRH_New_Variety_relFreeAb_map(v_C_111_, v_inst_112_, v_V_113_, v_V_x27_114_, v_U_115_, v_U_x27_116_, v_u_117_, v_h_x27_118_);
lean_dec_ref(v_inst_112_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict___redArg(lean_object* v_V_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___x_124_; 
v___x_122_ = lp_mathlib_CategoryTheory_Subfunctor_toFunctor___redArg(v_V_121_);
v___f_123_ = ((lean_object*)(lp_GRH_New_Variety_relFreeAb_restrict___redArg___closed__0));
lean_inc_ref(v___x_122_);
v___x_124_ = lp_GRH_New_Variety_relFreeAb_map___redArg(v___x_122_, v___x_122_, v___f_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict(lean_object* v_C_125_, lean_object* v_inst_126_, lean_object* v_V_127_, lean_object* v_U_128_, lean_object* v_A_129_, lean_object* v_B_130_, lean_object* v_h_131_){
_start:
{
lean_object* v___x_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v___x_132_ = lp_mathlib_CategoryTheory_Subfunctor_toFunctor___redArg(v_V_127_);
v___f_133_ = ((lean_object*)(lp_GRH_New_Variety_relFreeAb_restrict___redArg___closed__0));
lean_inc_ref(v___x_132_);
v___x_134_ = lp_GRH_New_Variety_relFreeAb_map___redArg(v___x_132_, v___x_132_, v___f_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_restrict___boxed(lean_object* v_C_135_, lean_object* v_inst_136_, lean_object* v_V_137_, lean_object* v_U_138_, lean_object* v_A_139_, lean_object* v_B_140_, lean_object* v_h_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = lp_GRH_New_Variety_relFreeAb_restrict(v_C_135_, v_inst_136_, v_V_137_, v_U_138_, v_A_139_, v_B_140_, v_h_141_);
lean_dec_ref(v_inst_136_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod___redArg(lean_object* v_V_143_, lean_object* v_X_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_obj_148_; lean_object* v_map_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_obj_152_; lean_object* v_map_153_; lean_object* v___x_154_; lean_object* v_toSemiCartesianMonoidalCategory_155_; lean_object* v_obj_156_; lean_object* v_toMonoidalCategory_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_obj_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; 
v___x_145_ = lp_mathlib_CategoryTheory_typesCartesianMonoidalCategory;
v___x_146_ = lp_mathlib_AddCommGrpCat_instCategory;
v___x_147_ = lean_obj_once(&lp_GRH_New_Variety_freeAb_prod___redArg___closed__0, &lp_GRH_New_Variety_freeAb_prod___redArg___closed__0_once, _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__0);
v_obj_148_ = lean_ctor_get(v___x_147_, 0);
v_map_149_ = lean_ctor_get(v___x_147_, 1);
lean_inc_ref_n(v_V_143_, 3);
v___x_150_ = lp_GRH_New_Variety_relFreeAb___redArg(v_V_143_);
lean_inc_n(v_obj_148_, 2);
lean_inc_ref(v___x_150_);
v___x_151_ = lean_apply_1(v_obj_148_, v___x_150_);
v_obj_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_n(v_obj_152_, 2);
v_map_153_ = lean_ctor_get(v___x_151_, 1);
lean_inc(v_map_153_);
lean_dec_ref(v___x_151_);
v___x_154_ = lean_obj_once(&lp_GRH_New_Variety_freeAb_prod___redArg___closed__1, &lp_GRH_New_Variety_freeAb_prod___redArg___closed__1_once, _init_lp_GRH_New_Variety_freeAb_prod___redArg___closed__1);
v_toSemiCartesianMonoidalCategory_155_ = lean_ctor_get(v___x_145_, 0);
v_obj_156_ = lean_ctor_get(v___x_154_, 0);
v_toMonoidalCategory_157_ = lean_ctor_get(v_toSemiCartesianMonoidalCategory_155_, 0);
lean_inc_ref_n(v_X_144_, 3);
v___x_158_ = lp_GRH_New_Variety_relFreeAb___redArg(v_X_144_);
lean_inc_ref(v_toMonoidalCategory_157_);
v___x_159_ = lp_mathlib_CategoryTheory_Monoidal_FunctorCategory_tensorObj___redArg(v_toMonoidalCategory_157_, v_V_143_, v_X_144_);
lean_inc_n(v_obj_156_, 3);
v___x_160_ = lean_apply_1(v_obj_156_, v___x_159_);
v___x_161_ = lean_apply_1(v_obj_156_, v_V_143_);
lean_inc_ref(v___x_161_);
v___x_162_ = lean_apply_1(v_obj_148_, v___x_161_);
v_obj_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_obj_163_);
lean_dec_ref(v___x_162_);
lean_inc_ref(v___x_158_);
v___x_164_ = lean_apply_1(v_obj_152_, v___x_158_);
v___x_165_ = lean_apply_1(v_obj_156_, v_X_144_);
lean_inc_ref_n(v___x_165_, 3);
v___x_166_ = lean_apply_1(v_obj_163_, v___x_165_);
v___x_167_ = lp_GRH_New_Variety_freeAb_prod___redArg(v_V_143_, v_X_144_);
v___x_168_ = lean_apply_1(v_obj_152_, v___x_165_);
v___f_169_ = ((lean_object*)(lp_GRH_New_Variety_relFreeAb_map___redArg___closed__0));
lean_inc(v_map_149_);
v___x_170_ = lean_apply_4(v_map_149_, v___x_161_, v___x_150_, v___f_169_, v___x_165_);
v___x_171_ = lean_apply_3(v_map_153_, v___x_165_, v___x_158_, v___f_169_);
lean_inc_ref(v___x_164_);
lean_inc_ref(v___x_166_);
v___f_172_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0), 7, 6);
lean_closure_set(v___f_172_, 0, v___x_146_);
lean_closure_set(v___f_172_, 1, v___x_166_);
lean_closure_set(v___f_172_, 2, v___x_168_);
lean_closure_set(v___f_172_, 3, v___x_164_);
lean_closure_set(v___f_172_, 4, v___x_170_);
lean_closure_set(v___f_172_, 5, v___x_171_);
v___f_173_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0), 7, 6);
lean_closure_set(v___f_173_, 0, v___x_146_);
lean_closure_set(v___f_173_, 1, v___x_160_);
lean_closure_set(v___f_173_, 2, v___x_166_);
lean_closure_set(v___f_173_, 3, v___x_164_);
lean_closure_set(v___f_173_, 4, v___x_167_);
lean_closure_set(v___f_173_, 5, v___f_172_);
v___f_174_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abCoker_desc___redArg___lam__0), 3, 1);
lean_closure_set(v___f_174_, 0, v___f_173_);
return v___f_174_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod(lean_object* v_C_175_, lean_object* v_inst_176_, lean_object* v_V_177_, lean_object* v_X_178_, lean_object* v_U_179_, lean_object* v_W_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lp_GRH_New_Variety_relFreeAb_prod___redArg(v_V_177_, v_X_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_relFreeAb_prod___boxed(lean_object* v_C_182_, lean_object* v_inst_183_, lean_object* v_V_184_, lean_object* v_X_185_, lean_object* v_U_186_, lean_object* v_W_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = lp_GRH_New_Variety_relFreeAb_prod(v_C_182_, v_inst_183_, v_V_184_, v_X_185_, v_U_186_, v_W_187_);
lean_dec_ref(v_inst_183_);
return v_res_188_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_DenseSubfunctors(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Hodge_CupProduct(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_Etale_RelativeChains(uint8_t builtin) {
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
res = initialize_GRH_Lib_Cohomology_Etale_DenseSubfunctors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_Hodge_CupProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
