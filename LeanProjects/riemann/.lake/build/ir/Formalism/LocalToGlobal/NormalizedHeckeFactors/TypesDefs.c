// Lean compiler output
// Module: Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower public import Formalism.CyclotomicNorms.StatementT
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Data_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__0 = (const lean_object*)&lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__0_value;
static const lean_closure_object lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__0_value)} };
static const lean_object* lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__1 = (const lean_object*)&lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG___redArg___lam__0(lean_object* v_00_u03c7_4_, lean_object* v_00_u03c8_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v_re_9_; lean_object* v_im_10_; lean_object* v_re_11_; lean_object* v_im_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_22_; 
lean_inc(v_x_6_);
v___x_7_ = lean_apply_1(v_00_u03c7_4_, v_x_6_);
v___x_8_ = lean_apply_1(v_00_u03c8_5_, v_x_6_);
v_re_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_re_9_);
v_im_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_im_10_);
lean_dec_ref(v___x_8_);
v_re_11_ = lean_ctor_get(v___x_7_, 0);
v_im_12_ = lean_ctor_get(v___x_7_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_22_ == 0)
{
v___x_14_ = v___x_7_;
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_im_12_);
lean_inc(v_re_11_);
lean_dec(v___x_7_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_22_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___f_16_; lean_object* v___x_18_; 
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(v___f_16_, 0, v_im_10_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 1, v___f_16_);
lean_ctor_set(v___x_14_, 0, v_re_9_);
v___x_18_ = v___x_14_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_re_9_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___f_16_);
v___x_18_ = v_reuseFailAlloc_21_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___f_19_; lean_object* v___x_20_; 
v___f_19_ = ((lean_object*)(lp_tree_Formalism_L2_NT_ipG___redArg___lam__0___closed__1));
v___x_20_ = lp_mathlib_Complex_mulAux___redArg(v___f_19_, v_re_11_, v_im_12_, v___x_18_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG___redArg(lean_object* v_inst_23_, lean_object* v_00_u03c7_24_, lean_object* v_00_u03c8_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___f_26_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NT_ipG___redArg___lam__0), 3, 2);
lean_closure_set(v___f_26_, 0, v_00_u03c7_24_);
lean_closure_set(v___f_26_, 1, v_00_u03c8_25_);
v___x_27_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_28_ = lp_mathlib_Finset_sum___redArg(v___x_27_, v_inst_23_, v___f_26_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_ipG(lean_object* v_G_29_, lean_object* v_inst_30_, lean_object* v_00_u03c7_31_, lean_object* v_00_u03c8_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_tree_Formalism_L2_NT_ipG___redArg(v_inst_30_, v_00_u03c7_31_, v_00_u03c8_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs___lam__0(lean_object* v_i_34_, lean_object* v_c_35_, lean_object* v_j_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = lean_nat_dec_lt(v_j_36_, v_i_34_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; 
lean_dec(v_j_36_);
lean_dec_ref(v_c_35_);
v___x_38_ = lean_unsigned_to_nat(0u);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = lean_apply_1(v_c_35_, v_j_36_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs___lam__0___boxed(lean_object* v_i_40_, lean_object* v_c_41_, lean_object* v_j_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lp_tree_Formalism_L2_NT_offs___lam__0(v_i_40_, v_c_41_, v_j_42_);
lean_dec(v_i_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_offs(lean_object* v_m_44_, lean_object* v_c_45_, lean_object* v_i_46_){
_start:
{
lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___f_47_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_NT_offs___lam__0___boxed), 3, 2);
lean_closure_set(v___f_47_, 0, v_i_46_);
lean_closure_set(v___f_47_, 1, v_c_45_);
v___x_48_ = l_List_finRange(v_m_44_);
v___x_49_ = lp_mathlib_Finset_sum___at___00Fin_accumulate_spec__0___redArg(v___x_48_, v___f_47_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___redArg(lean_object* v_inst_50_, lean_object* v_m_51_, lean_object* v_r_52_, lean_object* v_c_53_, lean_object* v_i_54_, lean_object* v_M_55_, lean_object* v_a_56_, lean_object* v_b_57_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = lp_tree_Formalism_L2_NT_offs(v_m_51_, v_c_53_, v_i_54_);
v___x_65_ = lean_nat_add(v___x_64_, v_a_56_);
v___x_66_ = lean_nat_dec_lt(v___x_65_, v_r_52_);
if (v___x_66_ == 0)
{
lean_dec(v___x_65_);
lean_dec(v___x_64_);
lean_dec(v_M_55_);
goto v___jp_58_;
}
else
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_nat_add(v___x_64_, v_b_57_);
lean_dec(v___x_64_);
v___x_68_ = lean_nat_dec_lt(v___x_67_, v_r_52_);
if (v___x_68_ == 0)
{
lean_dec(v___x_67_);
lean_dec(v___x_65_);
lean_dec(v_M_55_);
goto v___jp_58_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = lean_apply_2(v_M_55_, v___x_65_, v___x_67_);
return v___x_69_;
}
}
v___jp_58_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_toSemiring_61_; lean_object* v___x_62_; lean_object* v_toZero_63_; 
v___x_59_ = lp_mathlib_Field_toSemifield___redArg(v_inst_50_);
v___x_60_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_59_);
v_toSemiring_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_toSemiring_61_);
lean_dec_ref(v___x_60_);
v___x_62_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_61_);
v_toZero_63_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_toZero_63_);
lean_dec_ref(v___x_62_);
return v_toZero_63_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___redArg___boxed(lean_object* v_inst_70_, lean_object* v_m_71_, lean_object* v_r_72_, lean_object* v_c_73_, lean_object* v_i_74_, lean_object* v_M_75_, lean_object* v_a_76_, lean_object* v_b_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_tree_Formalism_L2_NT_blkOf___redArg(v_inst_70_, v_m_71_, v_r_72_, v_c_73_, v_i_74_, v_M_75_, v_a_76_, v_b_77_);
lean_dec(v_b_77_);
lean_dec(v_a_76_);
lean_dec(v_r_72_);
lean_dec_ref(v_inst_70_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf(lean_object* v_F_79_, lean_object* v_inst_80_, lean_object* v_m_81_, lean_object* v_r_82_, lean_object* v_c_83_, lean_object* v_i_84_, lean_object* v_M_85_, lean_object* v_a_86_, lean_object* v_b_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_tree_Formalism_L2_NT_blkOf___redArg(v_inst_80_, v_m_81_, v_r_82_, v_c_83_, v_i_84_, v_M_85_, v_a_86_, v_b_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_blkOf___boxed(lean_object* v_F_89_, lean_object* v_inst_90_, lean_object* v_m_91_, lean_object* v_r_92_, lean_object* v_c_93_, lean_object* v_i_94_, lean_object* v_M_95_, lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lp_tree_Formalism_L2_NT_blkOf(v_F_89_, v_inst_90_, v_m_91_, v_r_92_, v_c_93_, v_i_94_, v_M_95_, v_a_96_, v_b_97_);
lean_dec(v_b_97_);
lean_dec(v_a_96_);
lean_dec(v_r_92_);
lean_dec_ref(v_inst_90_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___redArg(lean_object* v_00_u03c6_99_){
_start:
{
lean_inc_ref(v_00_u03c6_99_);
return v_00_u03c6_99_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___redArg___boxed(lean_object* v_00_u03c6_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_tree_Formalism_L2_NT_toZModAlgEquiv___redArg(v_00_u03c6_100_);
lean_dec_ref(v_00_u03c6_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv(lean_object* v_g_102_, lean_object* v_inst_103_, lean_object* v_00_u03c6_104_){
_start:
{
lean_inc_ref(v_00_u03c6_104_);
return v_00_u03c6_104_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_NT_toZModAlgEquiv___boxed(lean_object* v_g_105_, lean_object* v_inst_106_, lean_object* v_00_u03c6_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_tree_Formalism_L2_NT_toZModAlgEquiv(v_g_105_, v_inst_106_, v_00_u03c6_107_);
lean_dec_ref(v_00_u03c6_107_);
lean_dec(v_g_105_);
return v_res_108_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower(uint8_t builtin);
lean_object* initialize_tree_Formalism_CyclotomicNorms_StatementT(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_CyclotomicNorms_StatementT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
