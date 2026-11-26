// Lean compiler output
// Module: New.Spanning.Bessel.LargeFunction
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bessel.SchurBound public import New.Appendix.DiscreteSeries.PositionGroup public import New.Spanning.Bessel.Average public import New.Spanning.Bessel.Basic
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
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_PUnit_fintype;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instDivInvMonoid___redArg(lean_object*);
lean_object* lp_mathlib_SubgroupClass_toGroup___redArg(lean_object*);
lean_object* lp_mathlib_MulAut_conj___redArg(lean_object*);
lean_object* lp_GRH_New_DiscreteSeries_frameEquiv___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_OneHom_comp___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_SubgroupClass_inclusion___redArg___lam__0___boxed(lean_object*);
lean_object* lp_mathlib_MonoidHom_prodMap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_MonoidHom_domRestrict___redArg(lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__3(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_DiscreteSeries_besselPairHom___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_SubgroupClass_inclusion___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___closed__0 = (const lean_object*)&lp_GRH_New_DiscreteSeries_besselPairHom___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0(lean_object* v_decEqIndex_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_5_ = l_instDecidableEqSum_decEq___redArg(v_decEqIndex_1_, v___x_4_, v_a_2_, v_b_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0___boxed(lean_object* v_decEqIndex_6_, lean_object* v_a_7_, lean_object* v_b_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0(v_decEqIndex_6_, v_a_7_, v_b_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1(lean_object* v___f_11_, lean_object* v___x_12_, lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_instDecidableEqSum_decEq___redArg(v___f_11_, v___x_12_, v_a_13_, v_b_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1___boxed(lean_object* v___f_16_, lean_object* v___x_17_, lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1(v___f_16_, v___x_17_, v_a_18_, v_b_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2(lean_object* v_00_u03f1_22_, lean_object* v___f_23_, lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___f_27_; uint8_t v___x_28_; 
v___x_26_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_26_, 0, v_00_u03f1_22_);
lean_inc_ref(v___x_26_);
v___f_27_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_27_, 0, v___f_23_);
lean_closure_set(v___f_27_, 1, v___x_26_);
v___x_28_ = l_instDecidableEqSum_decEq___redArg(v___x_26_, v___f_27_, v_a_24_, v_b_25_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2___boxed(lean_object* v_00_u03f1_29_, lean_object* v___f_30_, lean_object* v_a_31_, lean_object* v_b_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2(v_00_u03f1_29_, v___f_30_, v_a_31_, v_b_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__3(lean_object* v___x_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_toFun_37_; lean_object* v___x_38_; 
v_toFun_37_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_toFun_37_);
lean_dec_ref(v___x_35_);
v___x_38_ = lean_apply_1(v_toFun_37_, v___y_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___redArg(lean_object* v_00_U0001d530_40_, lean_object* v_p_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; lean_object* v_00_u03f1_44_; lean_object* v_fintypeIndex_45_; lean_object* v_decEqIndex_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_toMonoid_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v_val_58_; lean_object* v_inv_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_75_; 
v___x_43_ = lp_mathlib_Complex_instCommSemiring;
v_00_u03f1_44_ = lean_ctor_get(v_00_U0001d530_40_, 0);
lean_inc_n(v_00_u03f1_44_, 2);
v_fintypeIndex_45_ = lean_ctor_get(v_00_U0001d530_40_, 1);
lean_inc(v_fintypeIndex_45_);
v_decEqIndex_46_ = lean_ctor_get(v_00_U0001d530_40_, 2);
lean_inc_ref(v_decEqIndex_46_);
lean_dec_ref(v_00_U0001d530_40_);
v___f_47_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_47_, 0, v_decEqIndex_46_);
v___x_48_ = lp_mathlib_PUnit_fintype;
v___f_49_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_49_, 0, v_00_u03f1_44_);
lean_closure_set(v___f_49_, 1, v___f_47_);
v___x_50_ = l_List_finRange(v_00_u03f1_44_);
v___x_51_ = lp_mathlib_Multiset_disjSum___redArg(v_fintypeIndex_45_, v___x_48_);
lean_inc(v___x_50_);
v___x_52_ = lp_mathlib_Multiset_disjSum___redArg(v___x_51_, v___x_50_);
v___x_53_ = lp_mathlib_Multiset_disjSum___redArg(v___x_50_, v___x_52_);
lean_inc(v___x_53_);
v___x_54_ = lp_mathlib_Matrix_semiring___redArg(v___x_43_, v___x_53_, v___f_49_);
v_toMonoid_55_ = lean_ctor_get(v___x_54_, 1);
lean_inc_ref(v_toMonoid_55_);
lean_dec_ref(v___x_54_);
v___x_56_ = lp_mathlib_Units_instDivInvMonoid___redArg(v_toMonoid_55_);
v___x_57_ = lp_mathlib_SubgroupClass_toGroup___redArg(v___x_56_);
v_val_58_ = lean_ctor_get(v_x_42_, 0);
v_inv_59_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_75_ == 0)
{
v___x_61_ = v_x_42_;
v_isShared_62_ = v_isSharedCheck_75_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_inv_59_);
lean_inc(v_val_58_);
lean_dec(v_x_42_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_75_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v_val_58_);
lean_ctor_set(v___x_61_, 0, v_inv_59_);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_inv_59_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_val_58_);
v___x_64_ = v_reuseFailAlloc_74_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_210__overap_65_; lean_object* v___x_66_; lean_object* v_toFun_67_; lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_210__overap_65_ = lp_mathlib_MulAut_conj___redArg(v___x_57_);
lean_dec_ref(v___x_57_);
v___x_66_ = lean_apply_1(v___x_210__overap_65_, v___x_64_);
v_toFun_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_toFun_67_);
lean_dec_ref(v___x_66_);
v___x_68_ = lp_GRH_New_DiscreteSeries_frameEquiv___redArg(v___x_53_, v_p_41_);
v___f_69_ = lean_alloc_closure((void*)(lp_GRH_New_DiscreteSeries_besselPairHom___redArg___lam__3), 2, 1);
lean_closure_set(v___f_69_, 0, v___x_68_);
v___f_70_ = lean_alloc_closure((void*)(lp_mathlib_OneHom_comp___redArg___lam__0), 3, 2);
lean_closure_set(v___f_70_, 0, v_toFun_67_);
lean_closure_set(v___f_70_, 1, v___f_69_);
v___f_71_ = ((lean_object*)(lp_GRH_New_DiscreteSeries_besselPairHom___redArg___closed__0));
v___x_72_ = lp_mathlib_MonoidHom_prodMap___redArg(v___f_70_, v___f_71_);
v___x_73_ = lp_mathlib_MonoidHom_domRestrict___redArg(v___x_72_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom(lean_object* v_00_U0001d530_76_, lean_object* v_00_u03b5_77_, lean_object* v_p_78_, lean_object* v_x_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_GRH_New_DiscreteSeries_besselPairHom___redArg(v_00_U0001d530_76_, v_p_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_DiscreteSeries_besselPairHom___boxed(lean_object* v_00_U0001d530_81_, lean_object* v_00_u03b5_82_, lean_object* v_p_83_, lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_GRH_New_DiscreteSeries_besselPairHom(v_00_U0001d530_81_, v_00_u03b5_82_, v_p_83_, v_x_84_);
lean_dec_ref(v_00_u03b5_82_);
return v_res_85_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_SchurBound(uint8_t builtin);
lean_object* initialize_GRH_New_Appendix_DiscreteSeries_PositionGroup(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_Average(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_Bessel_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_Bessel_LargeFunction(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bessel_SchurBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Appendix_DiscreteSeries_PositionGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_Average(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_Bessel_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
