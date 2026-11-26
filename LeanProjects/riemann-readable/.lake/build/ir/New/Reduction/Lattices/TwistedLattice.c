// Lean compiler output
// Module: New.Reduction.Lattices.TwistedLattice
// Imports: public import Init public meta import Init public import Lib.General.LinearAlgebra.GramDeterminant public import New.Reduction.Lattices.Colength public import New.Reduction.Lattices.Heights
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
extern lean_object* lp_mathlib_Complex_instNonUnitalCommRing;
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
extern lean_object* lp_mathlib_Complex_instAddCommMonoid;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instMul;
lean_object* lp_mathlib_Complex_instRatCast___lam__0(lean_object*);
lean_object* lp_batteries_Rat_cast(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_mulVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_instStarRing___lam__0(lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_conjAut___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instStarRing___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_conjAut___closed__0 = (const lean_object*)&lp_GRH_New_conjAut___closed__0_value;
static const lean_ctor_object lp_GRH_New_conjAut___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GRH_New_conjAut___closed__0_value),((lean_object*)&lp_GRH_New_conjAut___closed__0_value)}};
static const lean_object* lp_GRH_New_conjAut___closed__1 = (const lean_object*)&lp_GRH_New_conjAut___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_conjAut(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0;
static const lean_closure_object lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib_Complex_instRatCast___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__1 = (const lean_object*)&lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__1_value;
static const lean_closure_object lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_batteries_Rat_cast, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__1_value)} };
static const lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__2 = (const lean_object*)&lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_conjAut(lean_object* v_00_u03c3_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = ((lean_object*)(lp_GRH_New_conjAut___closed__1));
v___x_6_ = lp_mathlib_Equiv_trans___redArg(v___x_5_, v_00_u03c3_4_);
v___x_7_ = lp_mathlib_Equiv_trans___redArg(v___x_6_, v___x_5_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord___redArg(lean_object* v_inst_8_, lean_object* v_L_9_, lean_object* v_00_u03c3_10_, lean_object* v_y_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_lift_13_; lean_object* v_coord_14_; lean_object* v_toFun_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_lift_13_ = lean_ctor_get(v_L_9_, 2);
lean_inc(v_lift_13_);
v_coord_14_ = lean_ctor_get(v_L_9_, 5);
lean_inc_ref(v_coord_14_);
lean_dec_ref(v_L_9_);
v_toFun_15_ = lean_ctor_get(v_00_u03c3_10_, 0);
lean_inc(v_toFun_15_);
lean_dec_ref(v_00_u03c3_10_);
v___x_16_ = lean_apply_2(v_lift_13_, v_inst_8_, v_y_11_);
v___x_17_ = lean_apply_2(v_coord_14_, v___x_16_, v_a_12_);
v___x_18_ = lean_apply_1(v_toFun_15_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord(lean_object* v_V_19_, lean_object* v_T_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_L_24_, lean_object* v_00_u03c3_25_, lean_object* v_y_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_GRH_New_TwistedLattice_conjCoord___redArg(v_inst_23_, v_L_24_, v_00_u03c3_25_, v_y_26_, v_a_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_conjCoord___boxed(lean_object* v_V_29_, lean_object* v_T_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_L_34_, lean_object* v_00_u03c3_35_, lean_object* v_y_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_TwistedLattice_conjCoord(v_V_29_, v_T_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_L_34_, v_00_u03c3_35_, v_y_36_, v_a_37_);
lean_dec(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg___lam__0(lean_object* v_inst_39_, lean_object* v_L_40_, lean_object* v_00_u03c3_41_, lean_object* v_y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_44_; lean_object* v_re_45_; lean_object* v_im_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v___x_44_ = lp_GRH_New_TwistedLattice_conjCoord___redArg(v_inst_39_, v_L_40_, v_00_u03c3_41_, v_y_42_, v___y_43_);
v_re_45_ = lean_ctor_get(v___x_44_, 0);
v_im_46_ = lean_ctor_get(v___x_44_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v___x_44_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_im_46_);
lean_inc(v_re_45_);
lean_dec(v___x_44_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___f_50_; lean_object* v___x_52_; 
v___f_50_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_50_, 0, v_im_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v___f_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_re_45_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___f_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
static lean_object* _init_lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lp_mathlib_Complex_instNonUnitalCommRing;
v___x_56_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt___redArg(lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_L_63_, lean_object* v_y_64_, lean_object* v_00_u03c3_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v_fintypeCoord_68_; lean_object* v_gramMatrix_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_re_77_; 
v___x_66_ = lp_mathlib_Complex_instAddCommMonoid;
v___x_67_ = lean_obj_once(&lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0, &lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0_once, _init_lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__0);
v_fintypeCoord_68_ = lean_ctor_get(v_L_63_, 4);
lean_inc_n(v_fintypeCoord_68_, 2);
v_gramMatrix_69_ = lean_ctor_get(v_L_63_, 6);
lean_inc_ref(v_gramMatrix_69_);
lean_inc(v_y_64_);
lean_inc_ref(v_00_u03c3_65_);
lean_inc_ref(v_L_63_);
lean_inc(v_inst_62_);
v___f_70_ = lean_alloc_closure((void*)(lp_GRH_New_TwistedLattice_normSqAt___redArg___lam__0), 5, 4);
lean_closure_set(v___f_70_, 0, v_inst_62_);
lean_closure_set(v___f_70_, 1, v_L_63_);
lean_closure_set(v___f_70_, 2, v_00_u03c3_65_);
lean_closure_set(v___f_70_, 3, v_y_64_);
v___x_71_ = lp_mathlib_Complex_instMul;
v___x_72_ = lean_alloc_closure((void*)(lp_GRH_New_TwistedLattice_conjCoord___boxed), 9, 8);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, lean_box(0));
lean_closure_set(v___x_72_, 2, v_inst_60_);
lean_closure_set(v___x_72_, 3, v_inst_61_);
lean_closure_set(v___x_72_, 4, v_inst_62_);
lean_closure_set(v___x_72_, 5, v_L_63_);
lean_closure_set(v___x_72_, 6, v_00_u03c3_65_);
lean_closure_set(v___x_72_, 7, v_y_64_);
v___x_73_ = ((lean_object*)(lp_GRH_New_TwistedLattice_normSqAt___redArg___closed__2));
v___x_74_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_map), 8, 6);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, lean_box(0));
lean_closure_set(v___x_74_, 2, lean_box(0));
lean_closure_set(v___x_74_, 3, lean_box(0));
lean_closure_set(v___x_74_, 4, v_gramMatrix_69_);
lean_closure_set(v___x_74_, 5, v___x_73_);
v___x_75_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_mulVec), 8, 7);
lean_closure_set(v___x_75_, 0, lean_box(0));
lean_closure_set(v___x_75_, 1, lean_box(0));
lean_closure_set(v___x_75_, 2, lean_box(0));
lean_closure_set(v___x_75_, 3, v___x_67_);
lean_closure_set(v___x_75_, 4, v_fintypeCoord_68_);
lean_closure_set(v___x_75_, 5, v___x_74_);
lean_closure_set(v___x_75_, 6, v___x_72_);
v___x_76_ = lp_mathlib_dotProduct___redArg(v_fintypeCoord_68_, v___x_71_, v___x_66_, v___f_70_, v___x_75_);
v_re_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_re_77_);
lean_dec(v___x_76_);
return v_re_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_TwistedLattice_normSqAt(lean_object* v_V_78_, lean_object* v_T_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_L_83_, lean_object* v_y_84_, lean_object* v_00_u03c3_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_GRH_New_TwistedLattice_normSqAt___redArg(v_inst_80_, v_inst_81_, v_inst_82_, v_L_83_, v_y_84_, v_00_u03c3_85_);
return v___x_86_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_LinearAlgebra_GramDeterminant(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Lattices_Colength(uint8_t builtin);
lean_object* initialize_GRH_New_Reduction_Lattices_Heights(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Reduction_Lattices_TwistedLattice(uint8_t builtin) {
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
res = initialize_GRH_Lib_General_LinearAlgebra_GramDeterminant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Lattices_Colength(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_New_Reduction_Lattices_Heights(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
