// Lean compiler output
// Module: New.Spanning.RemainingTerms.SchurOrbit
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.ColumnLattice public import New.Spanning.RemainingTerms.FrameParts public import New.Spanning.RemainingTerms.LinkLattice public import New.Spanning.RemainingTerms.SchurTest
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
lean_object* lp_mathlib_Fin_castLEEmb___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Filling_initialIsotropicIndex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Fin_castLEEmb___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Filling_initialIsotropicIndex___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Filling_initialIsotropicIndex___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___redArg(){
_start:
{
lean_object* v___f_3_; 
v___f_3_ = ((lean_object*)(lp_GRH_New_Filling_initialIsotropicIndex___redArg___closed__0));
return v___f_3_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_GRH_New_Filling_initialIsotropicIndex___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex(lean_object* v_00_U0001d530_6_, lean_object* v_j_7_){
_start:
{
lean_object* v___f_8_; 
v___f_8_ = ((lean_object*)(lp_GRH_New_Filling_initialIsotropicIndex___redArg___closed__0));
return v___f_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_initialIsotropicIndex___boxed(lean_object* v_00_U0001d530_9_, lean_object* v_j_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_GRH_New_Filling_initialIsotropicIndex(v_00_U0001d530_9_, v_j_10_);
lean_dec(v_j_10_);
lean_dec_ref(v_00_U0001d530_9_);
return v_res_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_ColumnLattice(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_FrameParts(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_LinkLattice(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_SchurTest(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_SchurOrbit(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_ColumnLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_FrameParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_LinkLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Spanning_RemainingTerms_SchurTest(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
