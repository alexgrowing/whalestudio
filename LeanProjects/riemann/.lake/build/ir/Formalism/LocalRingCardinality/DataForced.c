// Lean compiler output
// Module: Formalism.LocalRingCardinality.DataForced
// Imports: public import Init public meta import Init public import Formalism.LocalRingCardinality.DataParams₂ public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
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
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
lean_object* lp_tree_Formalism_MainNotions_G_plGG___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_sigW(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_wj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_tauPl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wPl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wPl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_tauPl(lean_object* v_D_1_, lean_object* v_z_2_){
_start:
{
lean_object* v_eTau_3_; lean_object* v___x_4_; lean_object* v_toFun_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_eTau_3_ = lean_ctor_get(v_D_1_, 5);
lean_inc_ref(v_eTau_3_);
lean_dec_ref(v_D_1_);
v___x_4_ = lp_mathlib_Equiv_symm___redArg(v_eTau_3_);
v_toFun_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v___x_4_);
v___x_6_ = lp_tree_Formalism_MainNotions_G_plGG___redArg(v_z_2_);
v___x_7_ = lean_apply_1(v_toFun_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wPl(lean_object* v_D_8_, lean_object* v_j_9_, lean_object* v_z_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc_ref(v_D_8_);
v___x_11_ = lp_tree_Formalism_BasicNotions_tauPl(v_D_8_, v_z_10_);
v___x_12_ = lp_tree_Formalism_BasicNotions_wj(v_D_8_, v_j_9_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_wPl___boxed(lean_object* v_D_13_, lean_object* v_j_14_, lean_object* v_z_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_tree_Formalism_BasicNotions_wPl(v_D_13_, v_j_14_, v_z_15_);
lean_dec(v_j_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0(lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = lean_int_neg(v_a_17_);
v___x_19_ = lean_int_dec_le(v_a_17_, v___x_18_);
if (v___x_19_ == 0)
{
lean_dec(v___x_18_);
lean_inc(v_a_17_);
return v_a_17_;
}
else
{
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0___boxed(lean_object* v_a_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0(v_a_20_);
lean_dec(v_a_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__0(lean_object* v_kaBig_22_, lean_object* v_j_23_, lean_object* v_00_u03c4_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_apply_3(v_kaBig_22_, v_j_23_, v_00_u03c4_24_, v_a_25_);
v___x_27_ = lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0(v___x_26_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__1(lean_object* v_kaSmall_28_, lean_object* v_j_29_, lean_object* v_00_u03c4_30_, lean_object* v_a_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_apply_3(v_kaSmall_28_, v_j_29_, v_00_u03c4_30_, v_a_31_);
v___x_33_ = lp_tree_abs___at___00Formalism_BasicNotions_fockDeg_spec__0(v___x_32_);
lean_dec(v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__2(lean_object* v_R_34_, lean_object* v_j_35_, lean_object* v_kaBig_36_, lean_object* v_kaSmall_37_, lean_object* v_00_u03c4_38_){
_start:
{
lean_object* v___x_39_; lean_object* v_fst_40_; lean_object* v_snd_41_; lean_object* v___f_42_; lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_39_ = lp_tree_Formalism_BasicNotions_Ranks_sigW(v_R_34_, v_j_35_);
v_fst_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_fst_40_);
v_snd_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_snd_41_);
lean_dec_ref(v___x_39_);
lean_inc(v_00_u03c4_38_);
lean_inc(v_j_35_);
v___f_42_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_fockDeg___lam__0), 4, 3);
lean_closure_set(v___f_42_, 0, v_kaBig_36_);
lean_closure_set(v___f_42_, 1, v_j_35_);
lean_closure_set(v___f_42_, 2, v_00_u03c4_38_);
v___f_43_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_fockDeg___lam__1), 4, 3);
lean_closure_set(v___f_43_, 0, v_kaSmall_37_);
lean_closure_set(v___f_43_, 1, v_j_35_);
lean_closure_set(v___f_43_, 2, v_00_u03c4_38_);
v___x_44_ = l_List_finRange(v_fst_40_);
v___x_45_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_44_, v___f_42_);
v___x_46_ = l_List_finRange(v_snd_41_);
v___x_47_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v___x_46_, v___f_43_);
v___x_48_ = lean_int_add(v___x_45_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg___lam__2___boxed(lean_object* v_R_49_, lean_object* v_j_50_, lean_object* v_kaBig_51_, lean_object* v_kaSmall_52_, lean_object* v_00_u03c4_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = lp_tree_Formalism_BasicNotions_fockDeg___lam__2(v_R_49_, v_j_50_, v_kaBig_51_, v_kaSmall_52_, v_00_u03c4_53_);
lean_dec_ref(v_R_49_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_BasicNotions_fockDeg(lean_object* v_D_55_, lean_object* v_j_56_){
_start:
{
lean_object* v_what_u2082_57_; lean_object* v_R_58_; lean_object* v_instTau_59_; lean_object* v_kaBig_60_; lean_object* v_kaSmall_61_; lean_object* v___f_62_; lean_object* v___x_63_; 
v_what_u2082_57_ = lean_ctor_get(v_D_55_, 4);
lean_inc_ref(v_what_u2082_57_);
v_R_58_ = lean_ctor_get(v_D_55_, 0);
lean_inc_ref(v_R_58_);
lean_dec_ref(v_D_55_);
v_instTau_59_ = lean_ctor_get(v_what_u2082_57_, 5);
lean_inc(v_instTau_59_);
v_kaBig_60_ = lean_ctor_get(v_what_u2082_57_, 44);
lean_inc_ref(v_kaBig_60_);
v_kaSmall_61_ = lean_ctor_get(v_what_u2082_57_, 45);
lean_inc_ref(v_kaSmall_61_);
lean_dec_ref(v_what_u2082_57_);
v___f_62_ = lean_alloc_closure((void*)(lp_tree_Formalism_BasicNotions_fockDeg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_62_, 0, v_R_58_);
lean_closure_set(v___f_62_, 1, v_j_56_);
lean_closure_set(v___f_62_, 2, v_kaBig_60_);
lean_closure_set(v___f_62_, 3, v_kaSmall_61_);
v___x_63_ = lp_tree_Finset_sum___at___00Formalism_MainNotions_G_Ar_spec__0___redArg(v_instTau_59_, v___f_62_);
return v___x_63_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalRingCardinality_DataForced(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataParams_u2082(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_GrowthBounds_IsResidueClassZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
