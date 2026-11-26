// Lean compiler output
// Module: Lib.Shimura.Uniformisation.BallModel
// Imports: public import Init public meta import Init public import Lib.Shimura.ThetaModuli.PELThetaTori public import Lib.Shimura.Transfer.MarkedPairs
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
extern lean_object* lp_mathlib_Complex_instCommSemiring;
lean_object* l_List_finRange(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_toLin_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul(lean_object*, lean_object*);
lean_object* l_instSMulOfMul___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoidHom_mulLeft___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_prodMap___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_piMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0;
static const lean_closure_object lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_mathlib___private_Mathlib_Basic_Real_Basic_0__Real_mul, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__1 = (const lean_object*)&lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__1_value;
static const lean_closure_object lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSMulOfMul___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__1_value)} };
static const lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__2 = (const lean_object*)&lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__2_value;
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__0(lean_object* v_toCMType_1_, lean_object* v_v_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_toCMType_1_, v_v_2_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__1(lean_object* v___x_5_, lean_object* v_val_6_, lean_object* v___f_7_, lean_object* v___f_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_re_11_; lean_object* v_im_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_re_11_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_re_11_);
v_im_12_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_im_12_);
lean_dec_ref(v___x_5_);
v___x_13_ = lp_mathlib_Matrix_map___redArg(v_val_6_, v___f_7_, v___y_9_, v___y_10_);
v___x_14_ = lp_mathlib_Complex_mulAux___redArg(v___f_8_, v_re_11_, v_im_12_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__2(lean_object* v_z_15_, lean_object* v_rank_16_, lean_object* v___x_17_, lean_object* v___x_18_, lean_object* v_toCMType_19_, lean_object* v_a_20_, lean_object* v___f_21_, lean_object* v_v_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_val_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_toLinearMap_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___x_32_; 
v_val_25_ = lean_ctor_get(v_z_15_, 0);
lean_inc(v_val_25_);
lean_dec_ref(v_z_15_);
v___x_26_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_26_, 0, v_rank_16_);
v___x_27_ = lp_mathlib_Matrix_toLin_x27___redArg(v___x_17_, v___x_26_, v___x_18_);
v_toLinearMap_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_toLinearMap_28_);
lean_dec_ref(v___x_27_);
lean_inc(v_v_22_);
lean_inc_ref(v_toCMType_19_);
v___f_29_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_29_, 0, v_toCMType_19_);
lean_closure_set(v___f_29_, 1, v_v_22_);
v___x_30_ = lean_apply_2(v_toCMType_19_, v_v_22_, v_a_20_);
v___f_31_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__1), 6, 4);
lean_closure_set(v___f_31_, 0, v___x_30_);
lean_closure_set(v___f_31_, 1, v_val_25_);
lean_closure_set(v___f_31_, 2, v___f_29_);
lean_closure_set(v___f_31_, 3, v___f_21_);
v___x_32_ = lean_apply_3(v_toLinearMap_28_, v___f_31_, v___y_23_, v___y_24_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__3(lean_object* v_N_33_, lean_object* v___f_34_, lean_object* v_re_35_, lean_object* v___f_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_apply_2(v_N_33_, v___y_37_, v___y_38_);
v___x_40_ = lp_mathlib_Complex_mulAux___redArg(v___f_34_, v_re_35_, v___f_36_, v___x_39_);
return v___x_40_;
}
}
static lean_object* _init_lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lp_mathlib_Complex_instNonUnitalCommRing;
v___x_42_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg(lean_object* v_00_u03a8_46_, lean_object* v_D_47_, lean_object* v_00_u03bc_48_, lean_object* v_N_49_, lean_object* v_z_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_toCMType_54_; lean_object* v_v_u2080_55_; lean_object* v___x_56_; lean_object* v_re_57_; lean_object* v_im_58_; lean_object* v_rank_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_toLinearMap_67_; lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_52_ = lean_obj_once(&lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0, &lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0_once, _init_lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__0);
v___x_53_ = lp_mathlib_Complex_instCommSemiring;
v_toCMType_54_ = lean_ctor_get(v_00_u03a8_46_, 0);
lean_inc_ref_n(v_toCMType_54_, 2);
v_v_u2080_55_ = lean_ctor_get(v_00_u03a8_46_, 1);
lean_inc(v_v_u2080_55_);
lean_dec_ref(v_00_u03a8_46_);
lean_inc(v_a_51_);
v___x_56_ = lean_apply_2(v_toCMType_54_, v_v_u2080_55_, v_a_51_);
v_re_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc_n(v_re_57_, 2);
v_im_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc_n(v_im_58_, 2);
lean_dec_ref(v___x_56_);
v_rank_59_ = lean_ctor_get(v_D_47_, 3);
lean_inc_n(v_rank_59_, 2);
lean_dec_ref(v_D_47_);
v___x_60_ = l_List_finRange(v_rank_59_);
v___x_61_ = l_List_lengthTR___redArg(v___x_60_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_sub(v___x_61_, v___x_62_);
lean_dec(v___x_61_);
lean_inc(v___x_63_);
v___x_64_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_64_, 0, v___x_63_);
v___x_65_ = l_List_finRange(v___x_63_);
v___x_66_ = lp_mathlib_Matrix_toLin_x27___redArg(v___x_53_, v___x_64_, v___x_65_);
v_toLinearMap_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_toLinearMap_67_);
lean_dec_ref(v___x_66_);
v___f_68_ = ((lean_object*)(lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___closed__2));
v___x_69_ = lp_mathlib_Complex_mulAux___redArg(v___f_68_, v_re_57_, v_im_58_, v_00_u03bc_48_);
v___x_70_ = lp_mathlib_AddMonoidHom_mulLeft___redArg(v___x_52_, v___x_69_);
v___f_71_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__2), 10, 7);
lean_closure_set(v___f_71_, 0, v_z_50_);
lean_closure_set(v___f_71_, 1, v_rank_59_);
lean_closure_set(v___f_71_, 2, v___x_53_);
lean_closure_set(v___f_71_, 3, v___x_60_);
lean_closure_set(v___f_71_, 4, v_toCMType_54_);
lean_closure_set(v___f_71_, 5, v_a_51_);
lean_closure_set(v___f_71_, 6, v___f_68_);
v___f_72_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_72_, 0, v_im_58_);
v___f_73_ = lean_alloc_closure((void*)(lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg___lam__3), 6, 4);
lean_closure_set(v___f_73_, 0, v_N_49_);
lean_closure_set(v___f_73_, 1, v___f_68_);
lean_closure_set(v___f_73_, 2, v_re_57_);
lean_closure_set(v___f_73_, 3, v___f_72_);
v___x_74_ = lean_apply_1(v_toLinearMap_67_, v___f_73_);
v___x_75_ = lp_mathlib_LinearMap_prodMap___redArg(v___x_70_, v___x_74_);
v___x_76_ = lp_mathlib_LinearMap_piMap___redArg(v___f_71_);
v___x_77_ = lp_mathlib_LinearMap_prodMap___redArg(v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd(lean_object* v_E_78_, lean_object* v_inst_79_, lean_object* v_00_u03a8_80_, lean_object* v_D_81_, lean_object* v_00_u03bc_82_, lean_object* v_N_83_, lean_object* v_z_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___redArg(v_00_u03a8_80_, v_D_81_, v_00_u03bc_82_, v_N_83_, v_z_84_, v_a_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd___boxed(lean_object* v_E_87_, lean_object* v_inst_88_, lean_object* v_00_u03a8_89_, lean_object* v_D_90_, lean_object* v_00_u03bc_91_, lean_object* v_N_92_, lean_object* v_z_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_GRH___private_Lib_Shimura_Uniformisation_BallModel_0__New_Variety_fibreEnd(v_E_87_, v_inst_88_, v_00_u03a8_89_, v_D_90_, v_00_u03bc_91_, v_N_92_, v_z_93_, v_a_94_);
lean_dec_ref(v_inst_88_);
return v_res_95_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(uint8_t builtin);
lean_object* initialize_GRH_Lib_Shimura_Transfer_MarkedPairs(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Shimura_Uniformisation_BallModel(uint8_t builtin) {
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
res = initialize_GRH_Lib_Shimura_ThetaModuli_PELThetaTori(builtin);
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
