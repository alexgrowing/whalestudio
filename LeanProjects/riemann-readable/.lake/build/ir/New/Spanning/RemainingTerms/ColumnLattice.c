// Lean compiler output
// Module: New.Spanning.RemainingTerms.ColumnLattice
// Imports: public import Init public meta import Init public import New.Spanning.RemainingTerms.FrameCount
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
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_q_2_, lean_object* v_v_3_, lean_object* v_l_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_re_8_; lean_object* v_im_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_17_; 
v___x_6_ = lean_apply_2(v_q_2_, v_a_5_, v_l_4_);
v___x_7_ = lean_apply_2(v_inst_1_, v_v_3_, v___x_6_);
v_re_8_ = lean_ctor_get(v___x_7_, 0);
v_im_9_ = lean_ctor_get(v___x_7_, 1);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_17_ == 0)
{
v___x_11_ = v___x_7_;
v_isShared_12_ = v_isSharedCheck_17_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_im_9_);
lean_inc(v_re_8_);
lean_dec(v___x_7_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_17_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___f_13_; lean_object* v___x_15_; 
v___f_13_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_13_, 0, v_im_9_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___f_13_);
v___x_15_ = v___x_11_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_re_8_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___f_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___redArg(lean_object* v_inst_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_conjColumnsAtInfinity___redArg___lam__0), 5, 1);
lean_closure_set(v___f_19_, 0, v_inst_18_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity(lean_object* v_E_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_00_U0001d530_23_, lean_object* v_00_u03b9_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(lp_GRH_New_Filling_conjColumnsAtInfinity___redArg___lam__0), 5, 1);
lean_closure_set(v___f_25_, 0, v_inst_22_);
return v___f_25_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_conjColumnsAtInfinity___boxed(lean_object* v_E_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_00_U0001d530_29_, lean_object* v_00_u03b9_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_GRH_New_Filling_conjColumnsAtInfinity(v_E_26_, v_inst_27_, v_inst_28_, v_00_U0001d530_29_, v_00_u03b9_30_);
lean_dec_ref(v_00_U0001d530_29_);
lean_dec_ref(v_inst_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___redArg(){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___redArg___boxed(lean_object* v___dummy_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = lp_GRH_New_Filling_integralColumns___redArg();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns(lean_object* v_E_36_, lean_object* v_inst_37_, lean_object* v_inst_38_, lean_object* v_00_U0001d530_39_, lean_object* v_00_u03b9_40_, lean_object* v_S_41_, lean_object* v_c_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_integralColumns___boxed(lean_object* v_E_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_00_U0001d530_47_, lean_object* v_00_u03b9_48_, lean_object* v_S_49_, lean_object* v_c_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_GRH_New_Filling_integralColumns(v_E_44_, v_inst_45_, v_inst_46_, v_00_U0001d530_47_, v_00_u03b9_48_, v_S_49_, v_c_50_);
lean_dec(v_c_50_);
lean_dec_ref(v_S_49_);
lean_dec_ref(v_00_U0001d530_47_);
lean_dec_ref(v_inst_46_);
lean_dec_ref(v_inst_45_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___redArg(){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_box(0);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___redArg___boxed(lean_object* v___dummy_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_GRH_New_Filling_columnLattice___redArg();
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice(lean_object* v_E_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_00_U0001d530_59_, lean_object* v_00_u03b9_60_, lean_object* v_S_61_, lean_object* v_c_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Filling_columnLattice___boxed(lean_object* v_E_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_00_U0001d530_67_, lean_object* v_00_u03b9_68_, lean_object* v_S_69_, lean_object* v_c_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lp_GRH_New_Filling_columnLattice(v_E_64_, v_inst_65_, v_inst_66_, v_00_U0001d530_67_, v_00_u03b9_68_, v_S_69_, v_c_70_);
lean_dec(v_c_70_);
lean_dec_ref(v_S_69_);
lean_dec_ref(v_00_U0001d530_67_);
lean_dec_ref(v_inst_66_);
lean_dec_ref(v_inst_65_);
return v_res_71_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Spanning_RemainingTerms_FrameCount(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Spanning_RemainingTerms_ColumnLattice(uint8_t builtin) {
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
res = initialize_GRH_New_Spanning_RemainingTerms_FrameCount(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
