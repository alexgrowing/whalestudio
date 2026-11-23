// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.RowFormsLemmas
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.RowForms public import Formalism.LocalToGlobal.Columns.GSetLemmas public import Formalism.LocalToGlobal.Columns.CoefColLemmas public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
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
lean_object* lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Ideal_Quotient_semiring___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_semiring___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Units_instMul___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__0(lean_object* v___x_1_, lean_object* v_n_2_, lean_object* v___x_3_, lean_object* v_a_4_, lean_object* v_snd_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toMonoid_10_; lean_object* v___x_11_; lean_object* v_val_12_; lean_object* v_inv_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_294__overap_16_; lean_object* v___x_17_; lean_object* v___x_295__overap_18_; lean_object* v___x_19_; 
v___x_7_ = lp_mathlib_Ideal_Quotient_semiring___redArg(v___x_1_, v___y_6_);
v___x_8_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_8_, 0, v_n_2_);
v___x_9_ = lp_mathlib_Matrix_semiring___redArg(v___x_7_, v___x_3_, v___x_8_);
v_toMonoid_10_ = lean_ctor_get(v___x_9_, 1);
lean_inc_ref(v_toMonoid_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lean_apply_1(v_a_4_, v___y_6_);
v_val_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_val_12_);
v_inv_13_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_inv_13_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_inv_13_);
lean_ctor_set(v___x_14_, 1, v_val_12_);
v___x_15_ = lean_apply_1(v_snd_5_, v___y_6_);
v___x_294__overap_16_ = lp_mathlib_Units_instMul___redArg(v_toMonoid_10_);
v___x_17_ = lean_apply_2(v___x_294__overap_16_, v___x_14_, v___x_15_);
v___x_295__overap_18_ = lp_mathlib_Units_instMul___redArg(v_toMonoid_10_);
lean_dec_ref(v_toMonoid_10_);
v___x_19_ = lean_apply_2(v___x_295__overap_18_, v___x_17_, v___x_11_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__1(lean_object* v___x_20_, lean_object* v_n_21_, lean_object* v___x_22_, lean_object* v_a_23_, lean_object* v_g_24_){
_start:
{
lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_34_; 
v_fst_25_ = lean_ctor_get(v_g_24_, 0);
v_snd_26_ = lean_ctor_get(v_g_24_, 1);
v_isSharedCheck_34_ = !lean_is_exclusive(v_g_24_);
if (v_isSharedCheck_34_ == 0)
{
v___x_28_ = v_g_24_;
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_snd_26_);
lean_inc(v_fst_25_);
lean_dec(v_g_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_34_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___f_30_; lean_object* v___x_32_; 
v___f_30_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_conjG___redArg___lam__0), 6, 5);
lean_closure_set(v___f_30_, 0, v___x_20_);
lean_closure_set(v___f_30_, 1, v_n_21_);
lean_closure_set(v___f_30_, 2, v___x_22_);
lean_closure_set(v___f_30_, 3, v_a_23_);
lean_closure_set(v___f_30_, 4, v_snd_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___f_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_fst_25_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___f_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__2(lean_object* v___x_35_, lean_object* v_n_36_, lean_object* v___x_37_, lean_object* v_a_38_, lean_object* v_snd_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_toMonoid_44_; lean_object* v___x_45_; lean_object* v_val_46_; lean_object* v_inv_47_; lean_object* v___x_48_; lean_object* v___x_308__overap_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_310__overap_52_; lean_object* v___x_53_; 
v___x_41_ = lp_mathlib_Ideal_Quotient_semiring___redArg(v___x_35_, v___y_40_);
v___x_42_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_42_, 0, v_n_36_);
v___x_43_ = lp_mathlib_Matrix_semiring___redArg(v___x_41_, v___x_37_, v___x_42_);
v_toMonoid_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc_ref(v_toMonoid_44_);
lean_dec_ref(v___x_43_);
v___x_45_ = lean_apply_1(v_a_38_, v___y_40_);
v_val_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_46_);
v_inv_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_inv_47_);
v___x_48_ = lean_apply_1(v_snd_39_, v___y_40_);
v___x_308__overap_49_ = lp_mathlib_Units_instMul___redArg(v_toMonoid_44_);
v___x_50_ = lean_apply_2(v___x_308__overap_49_, v___x_45_, v___x_48_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v_inv_47_);
lean_ctor_set(v___x_51_, 1, v_val_46_);
v___x_310__overap_52_ = lp_mathlib_Units_instMul___redArg(v_toMonoid_44_);
lean_dec_ref(v_toMonoid_44_);
v___x_53_ = lean_apply_2(v___x_310__overap_52_, v___x_50_, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg___lam__3(lean_object* v___x_54_, lean_object* v_n_55_, lean_object* v___x_56_, lean_object* v_a_57_, lean_object* v_g_58_){
_start:
{
lean_object* v_fst_59_; lean_object* v_snd_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_68_; 
v_fst_59_ = lean_ctor_get(v_g_58_, 0);
v_snd_60_ = lean_ctor_get(v_g_58_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_g_58_);
if (v_isSharedCheck_68_ == 0)
{
v___x_62_ = v_g_58_;
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_snd_60_);
lean_inc(v_fst_59_);
lean_dec(v_g_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_68_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___f_64_; lean_object* v___x_66_; 
v___f_64_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_conjG___redArg___lam__2), 6, 5);
lean_closure_set(v___f_64_, 0, v___x_54_);
lean_closure_set(v___f_64_, 1, v_n_55_);
lean_closure_set(v___f_64_, 2, v___x_56_);
lean_closure_set(v___f_64_, 3, v_a_57_);
lean_closure_set(v___f_64_, 4, v_snd_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___f_64_);
v___x_66_ = v___x_62_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_fst_59_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___f_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___redArg(lean_object* v_X_69_, lean_object* v_n_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_fieldE_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___f_76_; lean_object* v___x_77_; 
v_fieldE_72_ = lean_ctor_get(v_X_69_, 1);
lean_inc_ref(v_fieldE_72_);
lean_dec_ref(v_X_69_);
v___x_73_ = lp_mathlib_NumberField_instCommRingRingOfIntegers___redArg(v_fieldE_72_);
lean_inc_n(v_n_70_, 2);
v___x_74_ = l_List_finRange(v_n_70_);
lean_inc_ref(v_a_71_);
lean_inc(v___x_74_);
lean_inc_ref(v___x_73_);
v___f_75_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_conjG___redArg___lam__1), 5, 4);
lean_closure_set(v___f_75_, 0, v___x_73_);
lean_closure_set(v___f_75_, 1, v_n_70_);
lean_closure_set(v___f_75_, 2, v___x_74_);
lean_closure_set(v___f_75_, 3, v_a_71_);
v___f_76_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_conjG___redArg___lam__3), 5, 4);
lean_closure_set(v___f_76_, 0, v___x_73_);
lean_closure_set(v___f_76_, 1, v_n_70_);
lean_closure_set(v___f_76_, 2, v___x_74_);
lean_closure_set(v___f_76_, 3, v_a_71_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___f_76_);
lean_ctor_set(v___x_77_, 1, v___f_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG(lean_object* v_X_78_, lean_object* v_n_79_, lean_object* v_SG_80_, lean_object* v_00_u039b_81_, lean_object* v_a_82_, lean_object* v_ha_83_, lean_object* v_ha_x27_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_tree_Formalism_L2_Col_conjG___redArg(v_X_78_, v_n_79_, v_a_82_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_conjG___boxed(lean_object* v_X_86_, lean_object* v_n_87_, lean_object* v_SG_88_, lean_object* v_00_u039b_89_, lean_object* v_a_90_, lean_object* v_ha_91_, lean_object* v_ha_x27_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_L2_Col_conjG(v_X_86_, v_n_87_, v_SG_88_, v_00_u039b_89_, v_a_90_, v_ha_91_, v_ha_x27_92_);
lean_dec_ref(v_00_u039b_89_);
lean_dec(v_SG_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG___redArg(lean_object* v_w_94_){
_start:
{
return v_w_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG(lean_object* v_X_95_, lean_object* v_SG0_96_, lean_object* v_Q_97_, lean_object* v_w_98_){
_start:
{
return v_w_98_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_inlSG___boxed(lean_object* v_X_99_, lean_object* v_SG0_100_, lean_object* v_Q_101_, lean_object* v_w_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_tree_Formalism_L2_Col_inlSG(v_X_99_, v_SG0_100_, v_Q_101_, v_w_102_);
lean_dec(v_Q_101_);
lean_dec(v_SG0_100_);
lean_dec_ref(v_X_99_);
return v_res_103_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_CoefColLemmas(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowFormsLemmas(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_GSetLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_CoefColLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_ColFormsLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
