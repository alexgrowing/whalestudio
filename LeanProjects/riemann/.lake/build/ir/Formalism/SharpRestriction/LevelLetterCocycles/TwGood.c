// Lean compiler output
// Module: Formalism.SharpRestriction.LevelLetterCocycles.TwGood
// Imports: public import Init public meta import Init public import Formalism.SharpRestriction.ParConsts public import Formalism.LocalRingCardinality.DataNChTie public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
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
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_IntegralHeckeForms_ExpDat_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_IntegralHeckeForms_ExpDat_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twPack(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twPack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_NChoicePack(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_NChoicePack___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twEOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twEOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_IntegralHeckeForms_ExpDat_all(lean_object* v_D_1_, lean_object* v_N_2_, lean_object* v_X_3_, lean_object* v_Y_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_box(0);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_IntegralHeckeForms_ExpDat_all___boxed(lean_object* v_D_6_, lean_object* v_N_7_, lean_object* v_X_8_, lean_object* v_Y_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_tree_Formalism_MainNotions_IntegralHeckeForms_ExpDat_all(v_D_6_, v_N_7_, v_X_8_, v_Y_9_);
lean_dec_ref(v_Y_9_);
lean_dec_ref(v_X_8_);
lean_dec_ref(v_N_7_);
lean_dec_ref(v_D_6_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0___lam__0(lean_object* v_00_u03c8_11_, lean_object* v_g_12_){
_start:
{
lean_object* v___x_13_; lean_object* v_val_14_; lean_object* v_inv_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_22_; 
v___x_13_ = lean_apply_1(v_00_u03c8_11_, v_g_12_);
v_val_14_ = lean_ctor_get(v___x_13_, 0);
v_inv_15_ = lean_ctor_get(v___x_13_, 1);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
v___x_17_ = v___x_13_;
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_inv_15_);
lean_inc(v_val_14_);
lean_dec(v___x_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_22_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v_val_14_);
lean_ctor_set(v___x_17_, 0, v_inv_15_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_inv_15_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_val_14_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0(lean_object* v___x_23_, lean_object* v_i_24_, lean_object* v_Q_25_, lean_object* v_k_x27_26_, uint8_t v_b_27_, lean_object* v_00_u03c8_28_){
_start:
{
if (v_b_27_ == 0)
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_29_, 0, v_00_u03c8_28_);
return v___f_29_;
}
else
{
return v_00_u03c8_28_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0___boxed(lean_object* v___x_30_, lean_object* v_i_31_, lean_object* v_Q_32_, lean_object* v_k_x27_33_, lean_object* v_b_34_, lean_object* v_00_u03c8_35_){
_start:
{
uint8_t v_b_boxed_36_; lean_object* v_res_37_; 
v_b_boxed_36_ = lean_unbox(v_b_34_);
v_res_37_ = lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0(v___x_30_, v_i_31_, v_Q_32_, v_k_x27_33_, v_b_boxed_36_, v_00_u03c8_35_);
lean_dec(v_k_x27_33_);
lean_dec(v_Q_32_);
lean_dec(v_i_31_);
lean_dec_ref(v___x_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twPack(lean_object* v_D_38_, lean_object* v_i_39_, uint8_t v_b_40_, lean_object* v_Q_41_, lean_object* v_k_x27_42_, lean_object* v_00_u03c8_43_){
_start:
{
lean_object* v_ntw_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_ntw_44_ = lean_ctor_get(v_D_38_, 42);
v___x_45_ = lp_tree_Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0(v_ntw_44_, v_i_39_, v_Q_41_, v_k_x27_42_, v_b_40_, v_00_u03c8_43_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_k_x27_42_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_Q_41_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_48_, 0, v_i_39_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twPack___boxed(lean_object* v_D_49_, lean_object* v_i_50_, lean_object* v_b_51_, lean_object* v_Q_52_, lean_object* v_k_x27_53_, lean_object* v_00_u03c8_54_){
_start:
{
uint8_t v_b_boxed_55_; lean_object* v_res_56_; 
v_b_boxed_55_ = lean_unbox(v_b_51_);
v_res_56_ = lp_tree_Formalism_MainNotions_twPack(v_D_49_, v_i_50_, v_b_boxed_55_, v_Q_52_, v_k_x27_53_, v_00_u03c8_54_);
lean_dec_ref(v_D_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___redArg(lean_object* v_f_57_){
_start:
{
lean_inc_ref(v_f_57_);
return v_f_57_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___redArg___boxed(lean_object* v_f_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___redArg(v_f_58_);
lean_dec_ref(v_f_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0(lean_object* v___x_60_, lean_object* v_i_61_, lean_object* v_k_x27_62_, lean_object* v_Q_63_, lean_object* v_f_64_, lean_object* v_map__mul_65_){
_start:
{
lean_inc_ref(v_f_64_);
return v_f_64_;
}
}
LEAN_EXPORT lean_object* lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0___boxed(lean_object* v___x_66_, lean_object* v_i_67_, lean_object* v_k_x27_68_, lean_object* v_Q_69_, lean_object* v_f_70_, lean_object* v_map__mul_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_tree_MonoidHom_mk_x27___at___00Formalism_MainNotions_BlochKatoReduction_Gen_psiAt___at___00Formalism_MainNotions_twPack_spec__0_spec__0(v___x_66_, v_i_67_, v_k_x27_68_, v_Q_69_, v_f_70_, v_map__mul_71_);
lean_dec_ref(v_f_70_);
lean_dec(v_Q_69_);
lean_dec(v_k_x27_68_);
lean_dec(v_i_67_);
lean_dec_ref(v___x_66_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_NChoicePack(lean_object* v_D_73_, lean_object* v_C_74_, lean_object* v_w_75_){
_start:
{
lean_object* v_twI_76_; lean_object* v_sd_77_; lean_object* v_Q_78_; lean_object* v_k_x27_79_; lean_object* v_psi_x27_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v_twI_76_ = lean_ctor_get(v_C_74_, 0);
lean_inc(v_twI_76_);
v_sd_77_ = lean_ctor_get(v_C_74_, 1);
lean_inc_ref(v_sd_77_);
v_Q_78_ = lean_ctor_get(v_C_74_, 2);
lean_inc(v_Q_78_);
v_k_x27_79_ = lean_ctor_get(v_C_74_, 3);
lean_inc_ref(v_k_x27_79_);
v_psi_x27_80_ = lean_ctor_get(v_C_74_, 4);
lean_inc_ref(v_psi_x27_80_);
lean_dec_ref(v_C_74_);
lean_inc_n(v_w_75_, 4);
v___x_81_ = lean_apply_1(v_twI_76_, v_w_75_);
v___x_82_ = lean_apply_1(v_sd_77_, v_w_75_);
v___x_83_ = lean_apply_1(v_Q_78_, v_w_75_);
v___x_84_ = lean_apply_1(v_k_x27_79_, v_w_75_);
v___x_85_ = lean_apply_1(v_psi_x27_80_, v_w_75_);
v___x_86_ = lean_unbox(v___x_82_);
v___x_87_ = lp_tree_Formalism_MainNotions_twPack(v_D_73_, v___x_81_, v___x_86_, v___x_83_, v___x_84_, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_NChoicePack___boxed(lean_object* v_D_88_, lean_object* v_C_89_, lean_object* v_w_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_tree_Formalism_MainNotions_NChoicePack(v_D_88_, v_C_89_, v_w_90_);
lean_dec_ref(v_D_88_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twEOf(lean_object* v_D_92_, lean_object* v_T_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twEOf___boxed(lean_object* v_D_95_, lean_object* v_T_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = lp_tree_Formalism_MainNotions_twEOf(v_D_95_, v_T_96_);
lean_dec_ref(v_D_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twE(lean_object* v_eps_98_, lean_object* v_Fm_99_, lean_object* v_x_100_, lean_object* v_hx_101_, lean_object* v_i_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_MainNotions_twE___boxed(lean_object* v_eps_104_, lean_object* v_Fm_105_, lean_object* v_x_106_, lean_object* v_hx_107_, lean_object* v_i_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_tree_Formalism_MainNotions_twE(v_eps_104_, v_Fm_105_, v_x_106_, v_hx_107_, v_i_108_);
lean_dec(v_i_108_);
lean_dec(v_x_106_);
lean_dec_ref(v_Fm_105_);
lean_dec(v_eps_104_);
return v_res_109_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_ParConsts(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalRingCardinality_DataNChTie(uint8_t builtin);
lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_IntegralHeckeForms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_TwGood(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_ParConsts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalRingCardinality_DataNChTie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SharpRestriction_LevelLetterCocycles_IntegralHeckeForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
