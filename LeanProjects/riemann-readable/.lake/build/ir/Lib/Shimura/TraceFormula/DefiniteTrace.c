// Lean compiler output
// Module: Lib.Shimura.TraceFormula.DefiniteTrace
// Imports: public import Init public meta import Init public import Lib.Adelic.Reduction.FiniteVolume public import Lib.Shimura.AbelianScheme.Basic public import Lib.Shimura.Transfer.MarkedPairs
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
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v_snd_3_; lean_object* v_fst_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_7_; 
v_snd_3_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_snd_3_);
v_fst_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_4_);
lean_dec_ref(v_x_1_);
v_fst_5_ = lean_ctor_get(v_snd_3_, 0);
lean_inc(v_fst_5_);
v_snd_6_ = lean_ctor_get(v_snd_3_, 1);
lean_inc(v_snd_6_);
lean_dec(v_snd_3_);
v___x_7_ = lean_apply_3(v_h__1_2_, v_fst_4_, v_fst_5_, v_snd_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter(lean_object* v_E_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_n_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_00_U0001d511_14_, lean_object* v_motive_15_, lean_object* v_x_16_, lean_object* v_h__1_17_){
_start:
{
lean_object* v_snd_18_; lean_object* v_fst_19_; lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_22_; 
v_snd_18_ = lean_ctor_get(v_x_16_, 1);
lean_inc(v_snd_18_);
v_fst_19_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_fst_19_);
lean_dec_ref(v_x_16_);
v_fst_20_ = lean_ctor_get(v_snd_18_, 0);
lean_inc(v_fst_20_);
v_snd_21_ = lean_ctor_get(v_snd_18_, 1);
lean_inc(v_snd_21_);
lean_dec(v_snd_18_);
v___x_22_ = lean_apply_3(v_h__1_17_, v_fst_19_, v_fst_20_, v_snd_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter___boxed(lean_object* v_E_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_n_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_U0001d511_29_, lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_h__1_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_GRH___private_Lib_Shimura_TraceFormula_DefiniteTrace_0__New_Variety_DefiniteClass_orbit_match__1_splitter(v_E_23_, v_inst_24_, v_inst_25_, v_n_26_, v_inst_27_, v_inst_28_, v_00_U0001d511_29_, v_motive_30_, v_x_31_, v_h__1_32_);
lean_dec(v_00_U0001d511_29_);
lean_dec_ref(v_inst_28_);
lean_dec(v_inst_27_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Reduction_FiniteVolume(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_AbelianScheme_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Transfer_MarkedPairs(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_TraceFormula_DefiniteTrace(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Reduction_FiniteVolume(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_AbelianScheme_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Shimura_Transfer_MarkedPairs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
