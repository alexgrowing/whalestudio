// Lean compiler output
// Module: New.Congruences.FirstOrder.RibetMatrices
// Imports: public import Init public meta import Init public import New.Congruences.FirstOrder.FittingBlock
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
lean_object* l_Sum_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sum_elim___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Selmer_ribetGenerators___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Selmer_ribetGenerators___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Selmer_ribetGenerators___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Sum_elim, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_Selmer_ribetGenerators___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Selmer_ribetGenerators___redArg___closed__0_value)} };
static const lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Selmer_ribetGenerators___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0(lean_object* v_self_1_){
_start:
{
lean_inc(v_self_1_);
return v_self_1_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0___boxed(lean_object* v_self_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_GRH_New_Selmer_ribetGenerators___redArg___lam__0(v_self_2_);
lean_dec(v_self_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___redArg(lean_object* v_00_u03b4_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(lp_GRH_New_Selmer_ribetGenerators___redArg___closed__1));
v___x_10_ = l_Sum_elim___redArg(v_00_u03b4_7_, v___x_9_, v_a_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators(lean_object* v_G_11_, lean_object* v_W_x27_12_, lean_object* v_00_u03b4_13_, lean_object* v_s_u2080_14_, lean_object* v_s_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(lp_GRH_New_Selmer_ribetGenerators___redArg___closed__1));
v___x_18_ = l_Sum_elim___redArg(v_00_u03b4_13_, v___x_17_, v_a_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Selmer_ribetGenerators___boxed(lean_object* v_G_19_, lean_object* v_W_x27_20_, lean_object* v_00_u03b4_21_, lean_object* v_s_u2080_22_, lean_object* v_s_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_GRH_New_Selmer_ribetGenerators(v_G_19_, v_W_x27_20_, v_00_u03b4_21_, v_s_u2080_22_, v_s_23_, v_a_24_);
lean_dec(v_s_23_);
lean_dec(v_s_u2080_22_);
return v_res_25_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_FirstOrder_FittingBlock(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_FirstOrder_RibetMatrices(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_FirstOrder_FittingBlock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
