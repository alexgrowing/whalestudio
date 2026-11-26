// Lean compiler output
// Module: Lib.PadicHodge.Crystalline.HodgeTateJumps
// Imports: public import Init public meta import Init public import Lib.PadicHodge.Crystalline.HodgeTateForms
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
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___redArg___lam__0(lean_object* v_f_1_, lean_object* v_fst_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_f_1_, v_fst_2_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___redArg(lean_object* v_f_5_, lean_object* v_i_6_){
_start:
{
lean_object* v_fst_7_; lean_object* v___f_8_; 
v_fst_7_ = lean_ctor_get(v_i_6_, 0);
lean_inc(v_fst_7_);
lean_dec_ref(v_i_6_);
v___f_8_ = lean_alloc_closure((void*)(lp_GRH_New_Period_asSemilinear___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v_f_5_);
lean_closure_set(v___f_8_, 1, v_fst_7_);
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear(lean_object* v_p_9_, lean_object* v_inst_10_, lean_object* v_R_11_, lean_object* v_T_x27_12_, lean_object* v_00_u03b9_13_, lean_object* v_00_u03ba_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_S_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_f_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_GRH_New_Period_asSemilinear___redArg(v_f_24_, v_i_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Period_asSemilinear___boxed(lean_object** _args){
lean_object* v_p_27_ = _args[0];
lean_object* v_inst_28_ = _args[1];
lean_object* v_R_29_ = _args[2];
lean_object* v_T_x27_30_ = _args[3];
lean_object* v_00_u03b9_31_ = _args[4];
lean_object* v_00_u03ba_32_ = _args[5];
lean_object* v_inst_33_ = _args[6];
lean_object* v_inst_34_ = _args[7];
lean_object* v_inst_35_ = _args[8];
lean_object* v_S_36_ = _args[9];
lean_object* v_inst_37_ = _args[10];
lean_object* v_inst_38_ = _args[11];
lean_object* v_inst_39_ = _args[12];
lean_object* v_inst_40_ = _args[13];
lean_object* v_inst_41_ = _args[14];
lean_object* v_f_42_ = _args[15];
lean_object* v_i_43_ = _args[16];
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_Period_asSemilinear(v_p_27_, v_inst_28_, v_R_29_, v_T_x27_30_, v_00_u03b9_31_, v_00_u03ba_32_, v_inst_33_, v_inst_34_, v_inst_35_, v_S_36_, v_inst_37_, v_inst_38_, v_inst_39_, v_inst_40_, v_inst_41_, v_f_42_, v_i_43_);
lean_dec(v_inst_41_);
lean_dec(v_inst_39_);
lean_dec(v_inst_38_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_35_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
lean_dec(v_p_27_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicHodge_Crystalline_HodgeTateForms(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_PadicHodge_Crystalline_HodgeTateJumps(uint8_t builtin) {
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
res = initialize_GRH_Lib_PadicHodge_Crystalline_HodgeTateForms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
