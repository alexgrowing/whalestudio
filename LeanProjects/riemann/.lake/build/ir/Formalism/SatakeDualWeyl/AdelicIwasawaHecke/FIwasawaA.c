// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaA
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.StatementF public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
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
lean_object* lp_tree_Formalism_UG_antiJ___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_UG_cT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0(lean_object* v_n_1_, lean_object* v_x_2_, lean_object* v_00_u03c3_3_, lean_object* v_y_4_, lean_object* v_toMul_5_, lean_object* v_j_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_j_6_, v___x_7_);
v___x_9_ = lean_nat_sub(v_n_1_, v___x_8_);
lean_dec(v___x_8_);
v___x_10_ = lean_apply_1(v_x_2_, v___x_9_);
v___x_11_ = lean_apply_1(v_00_u03c3_3_, v___x_10_);
v___x_12_ = lean_apply_1(v_y_4_, v_j_6_);
v___x_13_ = lean_apply_2(v_toMul_5_, v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0___boxed(lean_object* v_n_14_, lean_object* v_x_15_, lean_object* v_00_u03c3_16_, lean_object* v_y_17_, lean_object* v_toMul_18_, lean_object* v_j_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0(v_n_14_, v_x_15_, v_00_u03c3_16_, v_y_17_, v_toMul_18_, v_j_19_);
lean_dec(v_n_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg(lean_object* v_inst_21_, lean_object* v_00_u03c3_22_, lean_object* v_n_23_, lean_object* v_x_24_, lean_object* v_y_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_toSemiring_28_; lean_object* v_toAddCommMonoid_29_; lean_object* v___x_30_; lean_object* v_toMul_31_; lean_object* v___x_32_; lean_object* v___f_33_; lean_object* v___x_34_; 
v___x_26_ = lp_mathlib_Field_toSemifield___redArg(v_inst_21_);
v___x_27_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_26_);
v_toSemiring_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_toSemiring_28_);
lean_dec_ref(v___x_27_);
v_toAddCommMonoid_29_ = lean_ctor_get(v_toSemiring_28_, 0);
lean_inc_ref(v_toAddCommMonoid_29_);
v___x_30_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_28_);
v_toMul_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_toMul_31_);
lean_dec_ref(v___x_30_);
lean_inc(v_n_23_);
v___x_32_ = l_List_finRange(v_n_23_);
v___f_33_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaH___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_33_, 0, v_n_23_);
lean_closure_set(v___f_33_, 1, v_x_24_);
lean_closure_set(v___f_33_, 2, v_00_u03c3_22_);
lean_closure_set(v___f_33_, 3, v_y_25_);
lean_closure_set(v___f_33_, 4, v_toMul_31_);
v___x_34_ = lp_mathlib_Finset_sum___redArg(v_toAddCommMonoid_29_, v___x_32_, v___f_33_);
lean_dec_ref(v_toAddCommMonoid_29_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___redArg___boxed(lean_object* v_inst_35_, lean_object* v_00_u03c3_36_, lean_object* v_n_37_, lean_object* v_x_38_, lean_object* v_y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_tree_Formalism_UG_P_fIwasawaH___redArg(v_inst_35_, v_00_u03c3_36_, v_n_37_, v_x_38_, v_y_39_);
lean_dec_ref(v_inst_35_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH(lean_object* v_L_41_, lean_object* v_inst_42_, lean_object* v_00_u03c3_43_, lean_object* v_n_44_, lean_object* v_x_45_, lean_object* v_y_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_UG_P_fIwasawaH___redArg(v_inst_42_, v_00_u03c3_43_, v_n_44_, v_x_45_, v_y_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaH___boxed(lean_object* v_L_48_, lean_object* v_inst_49_, lean_object* v_00_u03c3_50_, lean_object* v_n_51_, lean_object* v_x_52_, lean_object* v_y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_UG_P_fIwasawaH(v_L_48_, v_inst_49_, v_00_u03c3_50_, v_n_51_, v_x_52_, v_y_53_);
lean_dec_ref(v_inst_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0(lean_object* v_inst_55_, lean_object* v_n_56_, lean_object* v_a_57_, lean_object* v_j_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lp_tree_Formalism_UG_antiJ___redArg(v_inst_55_, v_n_56_, v_j_58_, v_a_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0___boxed(lean_object* v_inst_60_, lean_object* v_n_61_, lean_object* v_a_62_, lean_object* v_j_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0(v_inst_60_, v_n_61_, v_a_62_, v_j_63_);
lean_dec(v_j_63_);
lean_dec(v_a_62_);
lean_dec(v_n_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1(lean_object* v_inst_65_, lean_object* v_n_66_, lean_object* v_a_67_, lean_object* v_j_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_tree_Formalism_UG_antiJ___redArg(v_inst_65_, v_n_66_, v_a_67_, v_j_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1___boxed(lean_object* v_inst_70_, lean_object* v_n_71_, lean_object* v_a_72_, lean_object* v_j_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1(v_inst_70_, v_n_71_, v_a_72_, v_j_73_);
lean_dec(v_j_73_);
lean_dec(v_a_72_);
lean_dec(v_n_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__2(lean_object* v_00_u03c3_75_, lean_object* v_M_76_, lean_object* v_j_77_, lean_object* v_j_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_tree_Formalism_UG_cT___redArg(v_00_u03c3_75_, v_M_76_, v_j_78_, v_j_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3(lean_object* v_00_u03c3_80_, lean_object* v_M_81_, lean_object* v___x_82_, lean_object* v_toMul_83_, lean_object* v_toAddCommMonoid_84_, lean_object* v___f_85_, lean_object* v_j_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___x_88_; 
v___f_87_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__2), 4, 3);
lean_closure_set(v___f_87_, 0, v_00_u03c3_80_);
lean_closure_set(v___f_87_, 1, v_M_81_);
lean_closure_set(v___f_87_, 2, v_j_86_);
v___x_88_ = lp_mathlib_dotProduct___redArg(v___x_82_, v_toMul_83_, v_toAddCommMonoid_84_, v___f_85_, v___f_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3___boxed(lean_object* v_00_u03c3_89_, lean_object* v_M_90_, lean_object* v___x_91_, lean_object* v_toMul_92_, lean_object* v_toAddCommMonoid_93_, lean_object* v___f_94_, lean_object* v_j_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3(v_00_u03c3_89_, v_M_90_, v___x_91_, v_toMul_92_, v_toAddCommMonoid_93_, v___f_94_, v_j_95_);
lean_dec_ref(v_toAddCommMonoid_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv___redArg(lean_object* v_inst_97_, lean_object* v_00_u03c3_98_, lean_object* v_n_99_, lean_object* v_M_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_toSemiring_105_; lean_object* v___x_106_; lean_object* v_toMul_107_; lean_object* v_toAddCommMonoid_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___f_112_; lean_object* v___x_113_; 
v___x_103_ = lp_mathlib_Field_toSemifield___redArg(v_inst_97_);
v___x_104_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_103_);
v_toSemiring_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref_n(v_toSemiring_105_, 2);
lean_dec_ref(v___x_104_);
v___x_106_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_105_);
v_toMul_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_n(v_toMul_107_, 2);
lean_dec_ref(v___x_106_);
v_toAddCommMonoid_108_ = lean_ctor_get(v_toSemiring_105_, 0);
lean_inc_ref_n(v_toAddCommMonoid_108_, 2);
lean_dec_ref(v_toSemiring_105_);
lean_inc_n(v_n_99_, 2);
lean_inc_ref(v_inst_97_);
v___f_109_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_109_, 0, v_inst_97_);
lean_closure_set(v___f_109_, 1, v_n_99_);
lean_closure_set(v___f_109_, 2, v_a_102_);
v___f_110_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_110_, 0, v_inst_97_);
lean_closure_set(v___f_110_, 1, v_n_99_);
lean_closure_set(v___f_110_, 2, v_a_101_);
v___x_111_ = l_List_finRange(v_n_99_);
lean_inc(v___x_111_);
v___f_112_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaInv___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_112_, 0, v_00_u03c3_98_);
lean_closure_set(v___f_112_, 1, v_M_100_);
lean_closure_set(v___f_112_, 2, v___x_111_);
lean_closure_set(v___f_112_, 3, v_toMul_107_);
lean_closure_set(v___f_112_, 4, v_toAddCommMonoid_108_);
lean_closure_set(v___f_112_, 5, v___f_110_);
v___x_113_ = lp_mathlib_dotProduct___redArg(v___x_111_, v_toMul_107_, v_toAddCommMonoid_108_, v___f_112_, v___f_109_);
lean_dec_ref(v_toAddCommMonoid_108_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaInv(lean_object* v_L_114_, lean_object* v_inst_115_, lean_object* v_00_u03c3_116_, lean_object* v_n_117_, lean_object* v_M_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lp_tree_Formalism_UG_P_fIwasawaInv___redArg(v_inst_115_, v_00_u03c3_116_, v_n_117_, v_M_118_, v_a_119_, v_a_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaMk___redArg(lean_object* v_inst_122_, lean_object* v_00_u03c3_123_, lean_object* v_n_124_, lean_object* v_M_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_inc(v_M_125_);
v___x_126_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaInv), 7, 5);
lean_closure_set(v___x_126_, 0, lean_box(0));
lean_closure_set(v___x_126_, 1, v_inst_122_);
lean_closure_set(v___x_126_, 2, v_00_u03c3_123_);
lean_closure_set(v___x_126_, 3, v_n_124_);
lean_closure_set(v___x_126_, 4, v_M_125_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_M_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaMk(lean_object* v_L_128_, lean_object* v_inst_129_, lean_object* v_00_u03c3_130_, lean_object* v_n_131_, lean_object* v_M_132_, lean_object* v_hM_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lp_tree_Formalism_UG_P_fIwasawaMk___redArg(v_inst_129_, v_00_u03c3_130_, v_n_131_, v_M_132_);
return v___x_134_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_StatementF(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_StatementF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
