// Lean compiler output
// Module: Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
// Imports: public import Init public meta import Init public import Mathlib public import Formalism.QuotientMetricDivisors.ProdFormula public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Pi_addCommMonoid___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Function_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_diagonal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0(lean_object* v_toAddCommMonoid_1_, lean_object* v_i_2_){
_start:
{
lean_inc_ref(v_toAddCommMonoid_1_);
return v_toAddCommMonoid_1_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0___boxed(lean_object* v_toAddCommMonoid_3_, lean_object* v_i_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0(v_toAddCommMonoid_3_, v_i_4_);
lean_dec(v_i_4_);
lean_dec_ref(v_toAddCommMonoid_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__1(lean_object* v_00_u03b3_6_, lean_object* v_i_7_, lean_object* v_e_8_, lean_object* v_toMul_9_, lean_object* v_k_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
lean_inc(v_k_10_);
v___x_12_ = lean_apply_2(v_00_u03b3_6_, v_k_10_, v_i_7_);
v___x_13_ = lean_apply_2(v_e_8_, v_k_10_, v___y_11_);
v___x_14_ = lean_apply_2(v_toMul_9_, v___x_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg(lean_object* v_inst_15_, lean_object* v_d_16_, lean_object* v_e_17_, lean_object* v_00_u03b3_18_, lean_object* v_i_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_toSemiring_23_; lean_object* v_toAddCommMonoid_24_; lean_object* v___x_25_; lean_object* v_toMul_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_24__overap_31_; lean_object* v___x_32_; 
v___x_21_ = lp_mathlib_Field_toSemifield___redArg(v_inst_15_);
v___x_22_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_21_);
v_toSemiring_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_toSemiring_23_);
lean_dec_ref(v___x_22_);
v_toAddCommMonoid_24_ = lean_ctor_get(v_toSemiring_23_, 0);
lean_inc_ref(v_toAddCommMonoid_24_);
v___x_25_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_23_);
v_toMul_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_toMul_26_);
lean_dec_ref(v___x_25_);
v___f_27_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_27_, 0, v_toAddCommMonoid_24_);
v___f_28_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___lam__1), 6, 4);
lean_closure_set(v___f_28_, 0, v_00_u03b3_18_);
lean_closure_set(v___f_28_, 1, v_i_19_);
lean_closure_set(v___f_28_, 2, v_e_17_);
lean_closure_set(v___f_28_, 3, v_toMul_26_);
v___x_29_ = lp_mathlib_Pi_addCommMonoid___redArg(v___f_27_);
v___x_30_ = l_List_finRange(v_d_16_);
v___x_24__overap_31_ = lp_mathlib_Finset_sum___redArg(v___x_29_, v___x_30_, v___f_28_);
lean_dec_ref(v___x_29_);
v___x_32_ = lean_apply_1(v___x_24__overap_31_, v_a_20_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___redArg___boxed(lean_object* v_inst_33_, lean_object* v_d_34_, lean_object* v_e_35_, lean_object* v_00_u03b3_36_, lean_object* v_i_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_tree_Formalism_DivisionValues_idxChangeAct___redArg(v_inst_33_, v_d_34_, v_e_35_, v_00_u03b3_36_, v_i_37_, v_a_38_);
lean_dec_ref(v_inst_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct(lean_object* v_K_40_, lean_object* v_inst_41_, lean_object* v_d_42_, lean_object* v_e_43_, lean_object* v_00_u03b3_44_, lean_object* v_i_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_tree_Formalism_DivisionValues_idxChangeAct___redArg(v_inst_41_, v_d_42_, v_e_43_, v_00_u03b3_44_, v_i_45_, v_a_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeAct___boxed(lean_object* v_K_48_, lean_object* v_inst_49_, lean_object* v_d_50_, lean_object* v_e_51_, lean_object* v_00_u03b3_52_, lean_object* v_i_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lp_tree_Formalism_DivisionValues_idxChangeAct(v_K_48_, v_inst_49_, v_d_50_, v_e_51_, v_00_u03b3_52_, v_i_53_, v_a_54_);
lean_dec_ref(v_inst_49_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0(lean_object* v_toOne_56_, lean_object* v_x_57_){
_start:
{
lean_inc(v_toOne_56_);
return v_toOne_56_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0___boxed(lean_object* v_toOne_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0(v_toOne_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_toOne_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg___redArg(lean_object* v_inst_61_, lean_object* v_d_62_, lean_object* v_i_63_, lean_object* v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toSemiring_69_; lean_object* v___x_70_; lean_object* v_toZero_71_; lean_object* v___x_72_; lean_object* v_toRing_73_; lean_object* v___x_74_; lean_object* v_toAddMonoidWithOne_75_; lean_object* v_toOne_76_; lean_object* v___x_77_; lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_67_ = lp_mathlib_Field_toSemifield___redArg(v_inst_61_);
v___x_68_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_67_);
v_toSemiring_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toSemiring_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_69_);
v_toZero_71_ = lean_ctor_get(v___x_70_, 1);
lean_inc(v_toZero_71_);
lean_dec_ref(v___x_70_);
v___x_72_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_61_);
v_toRing_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_toRing_73_);
lean_dec_ref(v___x_72_);
v___x_74_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_73_);
v_toAddMonoidWithOne_75_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_toAddMonoidWithOne_75_);
lean_dec_ref(v___x_74_);
v_toOne_76_ = lean_ctor_get(v_toAddMonoidWithOne_75_, 2);
lean_inc(v_toOne_76_);
lean_dec_ref(v_toAddMonoidWithOne_75_);
v___x_77_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_77_, 0, v_d_62_);
v___f_78_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_78_, 0, v_toOne_76_);
lean_inc_ref(v___x_77_);
v___x_79_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_79_, 0, lean_box(0));
lean_closure_set(v___x_79_, 1, lean_box(0));
lean_closure_set(v___x_79_, 2, v___x_77_);
lean_closure_set(v___x_79_, 3, v___f_78_);
lean_closure_set(v___x_79_, 4, v_i_63_);
lean_closure_set(v___x_79_, 5, v_x_64_);
v___x_80_ = lp_mathlib_Matrix_diagonal___redArg(v___x_77_, v_toZero_71_, v___x_79_, v_a_65_, v_a_66_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_DivisionValues_idxChangeDg(lean_object* v_K_81_, lean_object* v_inst_82_, lean_object* v_d_83_, lean_object* v_i_84_, lean_object* v_x_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v_toSemiring_90_; lean_object* v___x_91_; lean_object* v_toZero_92_; lean_object* v___x_93_; lean_object* v_toRing_94_; lean_object* v___x_95_; lean_object* v_toAddMonoidWithOne_96_; lean_object* v_toOne_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_88_ = lp_mathlib_Field_toSemifield___redArg(v_inst_82_);
v___x_89_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_88_);
v_toSemiring_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_toSemiring_90_);
lean_dec_ref(v___x_89_);
v___x_91_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_90_);
v_toZero_92_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_toZero_92_);
lean_dec_ref(v___x_91_);
v___x_93_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_82_);
v_toRing_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_toRing_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_94_);
v_toAddMonoidWithOne_96_ = lean_ctor_get(v___x_95_, 1);
lean_inc_ref(v_toAddMonoidWithOne_96_);
lean_dec_ref(v___x_95_);
v_toOne_97_ = lean_ctor_get(v_toAddMonoidWithOne_96_, 2);
lean_inc(v_toOne_97_);
lean_dec_ref(v_toAddMonoidWithOne_96_);
v___x_98_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_98_, 0, v_d_83_);
v___f_99_ = lean_alloc_closure((void*)(lp_tree_Formalism_DivisionValues_idxChangeDg___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_99_, 0, v_toOne_97_);
lean_inc_ref(v___x_98_);
v___x_100_ = lean_alloc_closure((void*)(lp_mathlib_Function_update___boxed), 7, 6);
lean_closure_set(v___x_100_, 0, lean_box(0));
lean_closure_set(v___x_100_, 1, lean_box(0));
lean_closure_set(v___x_100_, 2, v___x_98_);
lean_closure_set(v___x_100_, 3, v___f_99_);
lean_closure_set(v___x_100_, 4, v_i_84_);
lean_closure_set(v___x_100_, 5, v_x_85_);
v___x_101_ = lp_mathlib_Matrix_diagonal___redArg(v___x_98_, v_toZero_92_, v___x_100_, v_a_86_, v_a_87_);
return v___x_101_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic(uint8_t builtin);
lean_object* initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange(uint8_t builtin) {
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
res = initialize_tree_Formalism_QuotientMetricDivisors_ProdFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
