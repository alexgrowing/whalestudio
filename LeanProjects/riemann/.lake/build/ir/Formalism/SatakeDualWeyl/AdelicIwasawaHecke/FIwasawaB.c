// Lean compiler output
// Module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB
// Imports: public import Init public meta import Init public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaA
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
lean_object* lp_mathlib_Equiv_refl(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instMulZeroClassOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0(lean_object* v_00_u03c0_1_, lean_object* v_inst_2_, lean_object* v_i_3_, lean_object* v_j_4_){
_start:
{
lean_object* v_toFun_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v_toFun_5_ = lean_ctor_get(v_00_u03c0_1_, 0);
lean_inc(v_toFun_5_);
lean_dec_ref(v_00_u03c0_1_);
v___x_6_ = lean_apply_1(v_toFun_5_, v_i_3_);
v___x_7_ = lean_nat_dec_eq(v___x_6_, v_j_4_);
lean_dec(v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toSemiring_10_; lean_object* v___x_11_; lean_object* v_toZero_12_; 
v___x_8_ = lp_mathlib_Field_toSemifield___redArg(v_inst_2_);
lean_dec_ref(v_inst_2_);
v___x_9_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_8_);
v_toSemiring_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_toSemiring_10_);
lean_dec_ref(v___x_9_);
v___x_11_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_10_);
v_toZero_12_ = lean_ctor_get(v___x_11_, 1);
lean_inc(v_toZero_12_);
lean_dec_ref(v___x_11_);
return v_toZero_12_;
}
else
{
lean_object* v___x_13_; lean_object* v_toRing_14_; lean_object* v___x_15_; lean_object* v_toAddMonoidWithOne_16_; lean_object* v_toOne_17_; 
v___x_13_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_2_);
v_toRing_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_toRing_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_14_);
v_toAddMonoidWithOne_16_ = lean_ctor_get(v___x_15_, 1);
lean_inc_ref(v_toAddMonoidWithOne_16_);
lean_dec_ref(v___x_15_);
v_toOne_17_ = lean_ctor_get(v_toAddMonoidWithOne_16_, 2);
lean_inc(v_toOne_17_);
lean_dec_ref(v_toAddMonoidWithOne_16_);
return v_toOne_17_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0___boxed(lean_object* v_00_u03c0_18_, lean_object* v_inst_19_, lean_object* v_i_20_, lean_object* v_j_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0(v_00_u03c0_18_, v_inst_19_, v_i_20_, v_j_21_);
lean_dec(v_j_21_);
return v_res_22_;
}
}
static lean_object* _init_lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_mathlib_Equiv_refl(lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___redArg(lean_object* v_inst_24_, lean_object* v_00_u03c0_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; lean_object* v_toFun_29_; lean_object* v___f_30_; lean_object* v___x_31_; 
v___x_28_ = lean_obj_once(&lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0, &lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0_once, _init_lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0);
v_toFun_29_ = lean_ctor_get(v___x_28_, 0);
v___f_30_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaP___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_30_, 0, v_00_u03c0_25_);
lean_closure_set(v___f_30_, 1, v_inst_24_);
lean_inc(v_toFun_29_);
v___x_31_ = lean_apply_3(v_toFun_29_, v___f_30_, v_a_26_, v_a_27_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP(lean_object* v_L_32_, lean_object* v_inst_33_, lean_object* v_n_34_, lean_object* v_00_u03c0_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_tree_Formalism_UG_P_fIwasawaP___redArg(v_inst_33_, v_00_u03c0_35_, v_a_36_, v_a_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaP___boxed(lean_object* v_L_39_, lean_object* v_inst_40_, lean_object* v_n_41_, lean_object* v_00_u03c0_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_tree_Formalism_UG_P_fIwasawaP(v_L_39_, v_inst_40_, v_n_41_, v_00_u03c0_42_, v_a_43_, v_a_44_);
lean_dec(v_n_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0(lean_object* v_z_46_, lean_object* v_n_47_, lean_object* v_e_48_, lean_object* v_00_u03c3_49_, lean_object* v_toMul_50_, lean_object* v_toAdd_51_, lean_object* v_toSub_52_, lean_object* v_c_53_, lean_object* v_toSemiring_54_, lean_object* v___x_55_, lean_object* v_i_56_, lean_object* v_j_57_){
_start:
{
lean_object* v___y_59_; uint8_t v___x_76_; 
v___x_76_ = lean_nat_dec_eq(v_i_56_, v_j_57_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_toZero_78_; 
lean_dec_ref(v___x_55_);
v___x_77_ = lp_mathlib_instMulZeroClassOfSemiring___redArg(v_toSemiring_54_);
v_toZero_78_ = lean_ctor_get(v___x_77_, 1);
lean_inc(v_toZero_78_);
lean_dec_ref(v___x_77_);
v___y_59_ = v_toZero_78_;
goto v___jp_58_;
}
else
{
lean_object* v_toAddMonoidWithOne_79_; lean_object* v_toOne_80_; 
lean_dec_ref(v_toSemiring_54_);
v_toAddMonoidWithOne_79_ = lean_ctor_get(v___x_55_, 1);
lean_inc_ref(v_toAddMonoidWithOne_79_);
lean_dec_ref(v___x_55_);
v_toOne_80_ = lean_ctor_get(v_toAddMonoidWithOne_79_, 2);
lean_inc(v_toOne_80_);
lean_dec_ref(v_toAddMonoidWithOne_79_);
v___y_59_ = v_toOne_80_;
goto v___jp_58_;
}
v___jp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
lean_inc(v_z_46_);
lean_inc(v_i_56_);
v___x_60_ = lean_apply_1(v_z_46_, v_i_56_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_j_57_, v___x_61_);
v___x_63_ = lean_nat_sub(v_n_47_, v___x_62_);
lean_dec(v___x_62_);
lean_inc(v_e_48_);
lean_inc(v___x_63_);
v___x_64_ = lean_apply_1(v_e_48_, v___x_63_);
lean_inc(v_00_u03c3_49_);
v___x_65_ = lean_apply_1(v_00_u03c3_49_, v___x_64_);
lean_inc_n(v_toMul_50_, 3);
lean_inc(v___x_65_);
v___x_66_ = lean_apply_2(v_toMul_50_, v___x_60_, v___x_65_);
lean_inc(v_toAdd_51_);
v___x_67_ = lean_apply_2(v_toAdd_51_, v___y_59_, v___x_66_);
v___x_68_ = lean_apply_1(v_e_48_, v_i_56_);
v___x_69_ = lean_apply_1(v_z_46_, v___x_63_);
v___x_70_ = lean_apply_1(v_00_u03c3_49_, v___x_69_);
lean_inc(v___x_68_);
v___x_71_ = lean_apply_2(v_toMul_50_, v___x_68_, v___x_70_);
v___x_72_ = lean_apply_2(v_toSub_52_, v___x_67_, v___x_71_);
v___x_73_ = lean_apply_2(v_toMul_50_, v_c_53_, v___x_68_);
v___x_74_ = lean_apply_2(v_toMul_50_, v___x_73_, v___x_65_);
v___x_75_ = lean_apply_2(v_toAdd_51_, v___x_72_, v___x_74_);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0___boxed(lean_object* v_z_81_, lean_object* v_n_82_, lean_object* v_e_83_, lean_object* v_00_u03c3_84_, lean_object* v_toMul_85_, lean_object* v_toAdd_86_, lean_object* v_toSub_87_, lean_object* v_c_88_, lean_object* v_toSemiring_89_, lean_object* v___x_90_, lean_object* v_i_91_, lean_object* v_j_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0(v_z_81_, v_n_82_, v_e_83_, v_00_u03c3_84_, v_toMul_85_, v_toAdd_86_, v_toSub_87_, v_c_88_, v_toSemiring_89_, v___x_90_, v_i_91_, v_j_92_);
lean_dec(v_j_92_);
lean_dec(v_n_82_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE___redArg(lean_object* v_inst_94_, lean_object* v_00_u03c3_95_, lean_object* v_n_96_, lean_object* v_e_97_, lean_object* v_z_98_, lean_object* v_c_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_toSemiring_104_; lean_object* v___x_105_; lean_object* v_toMul_106_; lean_object* v_toAdd_107_; lean_object* v___x_108_; lean_object* v_toRing_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_toSub_112_; lean_object* v___x_113_; lean_object* v_toFun_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v___x_102_ = lp_mathlib_Field_toSemifield___redArg(v_inst_94_);
v___x_103_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_102_);
v_toSemiring_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref_n(v_toSemiring_104_, 2);
lean_dec_ref(v___x_103_);
v___x_105_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_104_);
v_toMul_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_toMul_106_);
v_toAdd_107_ = lean_ctor_get(v___x_105_, 1);
lean_inc(v_toAdd_107_);
lean_dec_ref(v___x_105_);
v___x_108_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_94_);
v_toRing_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_toRing_109_);
lean_dec_ref(v___x_108_);
v___x_110_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_109_);
v___x_111_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_110_);
v_toSub_112_ = lean_ctor_get(v___x_111_, 2);
lean_inc(v_toSub_112_);
lean_dec_ref(v___x_111_);
v___x_113_ = lean_obj_once(&lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0, &lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0_once, _init_lp_tree_Formalism_UG_P_fIwasawaP___redArg___closed__0);
v_toFun_114_ = lean_ctor_get(v___x_113_, 0);
v___f_115_ = lean_alloc_closure((void*)(lp_tree_Formalism_UG_P_fIwasawaE___redArg___lam__0___boxed), 12, 10);
lean_closure_set(v___f_115_, 0, v_z_98_);
lean_closure_set(v___f_115_, 1, v_n_96_);
lean_closure_set(v___f_115_, 2, v_e_97_);
lean_closure_set(v___f_115_, 3, v_00_u03c3_95_);
lean_closure_set(v___f_115_, 4, v_toMul_106_);
lean_closure_set(v___f_115_, 5, v_toAdd_107_);
lean_closure_set(v___f_115_, 6, v_toSub_112_);
lean_closure_set(v___f_115_, 7, v_c_99_);
lean_closure_set(v___f_115_, 8, v_toSemiring_104_);
lean_closure_set(v___f_115_, 9, v___x_110_);
lean_inc(v_toFun_114_);
v___x_116_ = lean_apply_3(v_toFun_114_, v___f_115_, v_a_100_, v_a_101_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_UG_P_fIwasawaE(lean_object* v_L_117_, lean_object* v_inst_118_, lean_object* v_00_u03c3_119_, lean_object* v_n_120_, lean_object* v_e_121_, lean_object* v_z_122_, lean_object* v_c_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_tree_Formalism_UG_P_fIwasawaE___redArg(v_inst_118_, v_00_u03c3_119_, v_n_120_, v_e_121_, v_z_122_, v_c_123_, v_a_124_, v_a_125_);
return v___x_126_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
