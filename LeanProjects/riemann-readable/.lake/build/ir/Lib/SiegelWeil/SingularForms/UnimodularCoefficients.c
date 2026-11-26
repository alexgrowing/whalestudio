// Lean compiler output
// Module: Lib.SiegelWeil.SingularForms.UnimodularCoefficients
// Imports: public import Init public meta import Init public import Lib.SiegelWeil.SingularForms.CentreCoefficients public import Lib.Weil.MixedModel.AdaptedSplitting
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
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lp_GRH_New_Exchange_closureIntegers___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers(lean_object* v_E_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_S_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_closureIntegers___boxed(lean_object* v_E_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_S_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Exchange_closureIntegers(v_E_11_, v_inst_12_, v_inst_13_, v_inst_14_, v_S_15_);
lean_dec_ref(v_inst_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm___redArg(lean_object* v_P_17_){
_start:
{
lean_object* v_point_18_; lean_object* v_blockPoint_19_; lean_object* v_lineScalar_20_; lean_object* v_dualScalar_21_; lean_object* v_00_u03b3_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
v_point_18_ = lean_ctor_get(v_P_17_, 0);
v_blockPoint_19_ = lean_ctor_get(v_P_17_, 1);
v_lineScalar_20_ = lean_ctor_get(v_P_17_, 2);
v_dualScalar_21_ = lean_ctor_get(v_P_17_, 3);
v_00_u03b3_22_ = lean_ctor_get(v_P_17_, 4);
v_isSharedCheck_29_ = !lean_is_exclusive(v_P_17_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_P_17_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_00_u03b3_22_);
lean_inc(v_dualScalar_21_);
lean_inc(v_lineScalar_20_);
lean_inc(v_blockPoint_19_);
lean_inc(v_point_18_);
lean_dec(v_P_17_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_lineScalar_20_);
lean_ctor_set(v___x_24_, 2, v_dualScalar_21_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_point_18_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_blockPoint_19_);
lean_ctor_set(v_reuseFailAlloc_28_, 2, v_dualScalar_21_);
lean_ctor_set(v_reuseFailAlloc_28_, 3, v_lineScalar_20_);
lean_ctor_set(v_reuseFailAlloc_28_, 4, v_00_u03b3_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm(lean_object* v_E_30_, lean_object* v_n_31_, lean_object* v_n_u2081_32_, lean_object* v_n_u2082_33_, lean_object* v_p_34_, lean_object* v_inst_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_s_45_, lean_object* v_s_u2081_46_, lean_object* v_S_47_, lean_object* v_W_48_, lean_object* v_W_u2081_49_, lean_object* v_D_50_, lean_object* v_s_u2082_51_, lean_object* v_W_u2080_52_, lean_object* v_W_u2082_53_, lean_object* v_A_54_, lean_object* v_B_55_, lean_object* v_P_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_GRH_New_Exchange_StraightPoint_symm___redArg(v_P_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Exchange_StraightPoint_symm___boxed(lean_object** _args){
lean_object* v_E_58_ = _args[0];
lean_object* v_n_59_ = _args[1];
lean_object* v_n_u2081_60_ = _args[2];
lean_object* v_n_u2082_61_ = _args[3];
lean_object* v_p_62_ = _args[4];
lean_object* v_inst_63_ = _args[5];
lean_object* v_inst_64_ = _args[6];
lean_object* v_inst_65_ = _args[7];
lean_object* v_inst_66_ = _args[8];
lean_object* v_inst_67_ = _args[9];
lean_object* v_inst_68_ = _args[10];
lean_object* v_inst_69_ = _args[11];
lean_object* v_inst_70_ = _args[12];
lean_object* v_inst_71_ = _args[13];
lean_object* v_inst_72_ = _args[14];
lean_object* v_s_73_ = _args[15];
lean_object* v_s_u2081_74_ = _args[16];
lean_object* v_S_75_ = _args[17];
lean_object* v_W_76_ = _args[18];
lean_object* v_W_u2081_77_ = _args[19];
lean_object* v_D_78_ = _args[20];
lean_object* v_s_u2082_79_ = _args[21];
lean_object* v_W_u2080_80_ = _args[22];
lean_object* v_W_u2082_81_ = _args[23];
lean_object* v_A_82_ = _args[24];
lean_object* v_B_83_ = _args[25];
lean_object* v_P_84_ = _args[26];
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_GRH_New_Exchange_StraightPoint_symm(v_E_58_, v_n_59_, v_n_u2081_60_, v_n_u2082_61_, v_p_62_, v_inst_63_, v_inst_64_, v_inst_65_, v_inst_66_, v_inst_67_, v_inst_68_, v_inst_69_, v_inst_70_, v_inst_71_, v_inst_72_, v_s_73_, v_s_u2081_74_, v_S_75_, v_W_76_, v_W_u2081_77_, v_D_78_, v_s_u2082_79_, v_W_u2080_80_, v_W_u2082_81_, v_A_82_, v_B_83_, v_P_84_);
lean_dec_ref(v_B_83_);
lean_dec_ref(v_A_82_);
lean_dec_ref(v_W_u2082_81_);
lean_dec_ref(v_W_u2080_80_);
lean_dec_ref(v_s_u2082_79_);
lean_dec_ref(v_D_78_);
lean_dec_ref(v_W_u2081_77_);
lean_dec_ref(v_W_76_);
lean_dec_ref(v_s_u2081_74_);
lean_dec_ref(v_s_73_);
lean_dec_ref(v_inst_72_);
lean_dec(v_inst_71_);
lean_dec_ref(v_inst_70_);
lean_dec(v_inst_69_);
lean_dec_ref(v_inst_68_);
lean_dec(v_inst_67_);
lean_dec_ref(v_inst_66_);
lean_dec(v_inst_65_);
lean_dec_ref(v_inst_64_);
lean_dec_ref(v_inst_63_);
return v_res_85_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_SiegelWeil_SingularForms_CentreCoefficients(uint8_t builtin);
lean_object* initialize_GRH_Lib_Weil_MixedModel_AdaptedSplitting(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_SiegelWeil_SingularForms_UnimodularCoefficients(uint8_t builtin) {
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
res = initialize_GRH_Lib_SiegelWeil_SingularForms_CentreCoefficients(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Weil_MixedModel_AdaptedSplitting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
