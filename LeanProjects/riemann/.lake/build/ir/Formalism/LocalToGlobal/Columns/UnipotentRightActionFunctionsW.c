// Lean compiler output
// Module: Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.LocalToGlobal.Columns.RowForms public import Formalism.LocalToGlobal.Columns.HeckeSp public import Formalism.LocalToGlobal.Columns.MemWmPerp
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
lean_object* lp_mathlib_Monoid_toMulOneClass___redArg(lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_r(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_aPlus(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_tree_Formalism_BasicNotions_Ranks_nV(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_RowPar_eAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* lp_tree_Formalism_L2_Col_ofQ(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
static lean_once_cell_t lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamWQ(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamWQ___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamW(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamWQ(lean_object* v_R_3_, lean_object* v_S_4_, lean_object* v_i_5_){
_start:
{
lean_object* v_m_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_m_6_ = lean_ctor_get(v_R_3_, 2);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_i_5_, v___x_7_);
lean_inc_ref(v_S_4_);
v___x_9_ = lp_tree_Formalism_L2_Col_RowPar_aPlus(v_R_3_, v_S_4_, v_m_6_, v___x_8_);
v___x_10_ = lp_tree_Formalism_BasicNotions_Ranks_nV(v_R_3_);
v___x_11_ = lp_mathlib_Nat_cast___at___00CompareReals_instCommRingQ_spec__0(v___x_10_);
v___x_12_ = lean_obj_once(&lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0, &lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0_once, _init_lp_tree_Formalism_L2_Col_RowPar_lamWQ___closed__0);
v___x_13_ = l_Rat_div(v___x_11_, v___x_12_);
lean_dec_ref(v___x_11_);
v___x_14_ = l_Rat_add(v___x_9_, v___x_13_);
v___x_15_ = lean_nat_sub(v_m_6_, v___x_7_);
v___x_16_ = lp_tree_Formalism_L2_Col_RowPar_eAt(v_R_3_, v_S_4_, v___x_15_);
v___x_17_ = l_Rat_sub(v___x_14_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamWQ___boxed(lean_object* v_R_18_, lean_object* v_S_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_tree_Formalism_L2_Col_RowPar_lamWQ(v_R_18_, v_S_19_, v_i_20_);
lean_dec(v_i_20_);
lean_dec_ref(v_R_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_RowPar_lamW(lean_object* v_R_22_, lean_object* v_S_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lp_tree_Formalism_BasicNotions_Ranks_r(v_R_22_);
v___x_25_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_RowPar_lamWQ___boxed), 3, 2);
lean_closure_set(v___x_25_, 0, v_R_22_);
lean_closure_set(v___x_25_, 1, v_S_23_);
v___x_26_ = lp_tree_Formalism_L2_Col_ofQ(v___x_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW___redArg(lean_object* v_R_27_, lean_object* v_W_28_, lean_object* v_00_u03c4_29_){
_start:
{
lean_object* v_row_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_row_30_ = lean_ctor_get(v_W_28_, 0);
lean_inc_ref(v_row_30_);
lean_dec_ref(v_W_28_);
v___x_31_ = lean_apply_1(v_row_30_, v_00_u03c4_29_);
v___x_32_ = lp_tree_Formalism_L2_Col_RowPar_lamW(v_R_27_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW(lean_object* v_X_33_, lean_object* v_Word_34_, lean_object* v_R_35_, lean_object* v_W_36_, lean_object* v_00_u03c4_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_L2_Col_Wts_lamW___redArg(v_R_35_, v_W_36_, v_00_u03c4_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_Wts_lamW___boxed(lean_object* v_X_39_, lean_object* v_Word_40_, lean_object* v_R_41_, lean_object* v_W_42_, lean_object* v_00_u03c4_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_tree_Formalism_L2_Col_Wts_lamW(v_X_39_, v_Word_40_, v_R_41_, v_W_42_, v_00_u03c4_43_);
lean_dec_ref(v_X_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0(lean_object* v_toMonoid_45_, lean_object* v_x_46_){
_start:
{
lean_object* v___x_47_; lean_object* v_toOne_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v___x_47_ = lp_mathlib_Monoid_toMulOneClass___redArg(v_toMonoid_45_);
v_toOne_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v___x_47_, 1);
lean_dec(v_unused_56_);
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_toOne_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
lean_inc(v_toOne_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v_toOne_48_);
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_toOne_48_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_toOne_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0___boxed(lean_object* v_toMonoid_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0(v_toMonoid_57_, v_x_58_);
lean_dec_ref(v_x_58_);
lean_dec_ref(v_toMonoid_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg(lean_object* v_X_60_){
_start:
{
lean_object* v_fieldK_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_toSemiring_64_; lean_object* v_toMonoid_65_; lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___x_68_; 
v_fieldK_61_ = lean_ctor_get(v_X_60_, 2);
v___x_62_ = lp_mathlib_Field_toSemifield___redArg(v_fieldK_61_);
v___x_63_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_62_);
v_toSemiring_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_toSemiring_64_);
lean_dec_ref(v___x_63_);
v_toMonoid_65_ = lean_ctor_get(v_toSemiring_64_, 1);
lean_inc_ref(v_toMonoid_65_);
lean_dec_ref(v_toSemiring_64_);
v___x_66_ = lean_box(0);
v___f_67_ = lean_alloc_closure((void*)(lp_tree_Formalism_L2_Col_wmTyQ___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_67_, 0, v_toMonoid_65_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___f_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___redArg___boxed(lean_object* v_X_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_tree_Formalism_L2_Col_wmTyQ___redArg(v_X_69_);
lean_dec_ref(v_X_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ(lean_object* v_X_71_, lean_object* v_R_72_, lean_object* v_Q_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_tree_Formalism_L2_Col_wmTyQ___redArg(v_X_71_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Col_wmTyQ___boxed(lean_object* v_X_76_, lean_object* v_R_77_, lean_object* v_Q_78_, lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_tree_Formalism_L2_Col_wmTyQ(v_X_76_, v_R_77_, v_Q_78_, v_x_79_);
lean_dec(v_Q_78_);
lean_dec_ref(v_R_77_);
lean_dec_ref(v_X_76_);
return v_res_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_RowForms(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_MemWmPerp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_Columns_UnipotentRightActionFunctionsW(uint8_t builtin) {
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
res = initialize_tree_Formalism_LocalToGlobal_Columns_HeckeSp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_Columns_MemWmPerp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
