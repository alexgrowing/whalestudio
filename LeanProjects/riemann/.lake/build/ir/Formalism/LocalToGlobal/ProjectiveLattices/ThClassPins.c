// Lean compiler output
// Module: Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
// Imports: public import Init public meta import Init public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
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
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext___boxed(lean_object**);
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res___redArg(lean_object* v_y_1_){
_start:
{
lean_object* v_x_2_; lean_object* v_u_3_; lean_object* v_s_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_11_; 
v_x_2_ = lean_ctor_get(v_y_1_, 0);
v_u_3_ = lean_ctor_get(v_y_1_, 1);
v_s_4_ = lean_ctor_get(v_y_1_, 2);
v_isSharedCheck_11_ = !lean_is_exclusive(v_y_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_6_ = v_y_1_;
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_s_4_);
lean_inc(v_u_3_);
lean_inc(v_x_2_);
lean_dec(v_y_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_11_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_9_; 
if (v_isShared_7_ == 0)
{
v___x_9_ = v___x_6_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_x_2_);
lean_ctor_set(v_reuseFailAlloc_10_, 1, v_u_3_);
lean_ctor_set(v_reuseFailAlloc_10_, 2, v_s_4_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res(lean_object* v_E_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_H_16_, lean_object* v_Dw_17_, lean_object* v_l_18_, lean_object* v_c_19_, lean_object* v_c_x27_20_, lean_object* v_hle_21_, lean_object* v_Xo_22_, lean_object* v_S_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_h_27_, lean_object* v_y_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_tree_Formalism_L2_Pj_FrPt_res___redArg(v_y_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_res___boxed(lean_object** _args){
lean_object* v_E_30_ = _args[0];
lean_object* v_inst_31_ = _args[1];
lean_object* v_inst_32_ = _args[2];
lean_object* v_inst_33_ = _args[3];
lean_object* v_H_34_ = _args[4];
lean_object* v_Dw_35_ = _args[5];
lean_object* v_l_36_ = _args[6];
lean_object* v_c_37_ = _args[7];
lean_object* v_c_x27_38_ = _args[8];
lean_object* v_hle_39_ = _args[9];
lean_object* v_Xo_40_ = _args[10];
lean_object* v_S_41_ = _args[11];
lean_object* v_inst_42_ = _args[12];
lean_object* v_inst_43_ = _args[13];
lean_object* v_inst_44_ = _args[14];
lean_object* v_h_45_ = _args[15];
lean_object* v_y_46_ = _args[16];
_start:
{
lean_object* v_res_47_; 
v_res_47_ = lp_tree_Formalism_L2_Pj_FrPt_res(v_E_30_, v_inst_31_, v_inst_32_, v_inst_33_, v_H_34_, v_Dw_35_, v_l_36_, v_c_37_, v_c_x27_38_, v_hle_39_, v_Xo_40_, v_S_41_, v_inst_42_, v_inst_43_, v_inst_44_, v_h_45_, v_y_46_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_Xo_40_);
lean_dec_ref(v_l_36_);
lean_dec_ref(v_Dw_35_);
lean_dec_ref(v_H_34_);
lean_dec_ref(v_inst_31_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext___redArg(lean_object* v_y_48_){
_start:
{
lean_object* v_x_49_; lean_object* v_u_50_; lean_object* v_s_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_x_49_ = lean_ctor_get(v_y_48_, 0);
v_u_50_ = lean_ctor_get(v_y_48_, 1);
v_s_51_ = lean_ctor_get(v_y_48_, 2);
v_isSharedCheck_58_ = !lean_is_exclusive(v_y_48_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v_y_48_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_s_51_);
lean_inc(v_u_50_);
lean_inc(v_x_49_);
lean_dec(v_y_48_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_x_49_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_u_50_);
lean_ctor_set(v_reuseFailAlloc_57_, 2, v_s_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext(lean_object* v_E_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_H_63_, lean_object* v_Dw_64_, lean_object* v_l_65_, lean_object* v_c_66_, lean_object* v_c_x27_67_, lean_object* v_hle_68_, lean_object* v_Xo_69_, lean_object* v_S_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_h_74_, lean_object* v_y_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lp_tree_Formalism_L2_Pj_FrPt_ext___redArg(v_y_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_L2_Pj_FrPt_ext___boxed(lean_object** _args){
lean_object* v_E_77_ = _args[0];
lean_object* v_inst_78_ = _args[1];
lean_object* v_inst_79_ = _args[2];
lean_object* v_inst_80_ = _args[3];
lean_object* v_H_81_ = _args[4];
lean_object* v_Dw_82_ = _args[5];
lean_object* v_l_83_ = _args[6];
lean_object* v_c_84_ = _args[7];
lean_object* v_c_x27_85_ = _args[8];
lean_object* v_hle_86_ = _args[9];
lean_object* v_Xo_87_ = _args[10];
lean_object* v_S_88_ = _args[11];
lean_object* v_inst_89_ = _args[12];
lean_object* v_inst_90_ = _args[13];
lean_object* v_inst_91_ = _args[14];
lean_object* v_h_92_ = _args[15];
lean_object* v_y_93_ = _args[16];
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_tree_Formalism_L2_Pj_FrPt_ext(v_E_77_, v_inst_78_, v_inst_79_, v_inst_80_, v_H_81_, v_Dw_82_, v_l_83_, v_c_84_, v_c_x27_85_, v_hle_86_, v_Xo_87_, v_S_88_, v_inst_89_, v_inst_90_, v_inst_91_, v_h_92_, v_y_93_);
lean_dec_ref(v_inst_91_);
lean_dec_ref(v_inst_90_);
lean_dec_ref(v_inst_89_);
lean_dec_ref(v_Xo_87_);
lean_dec_ref(v_l_83_);
lean_dec_ref(v_Dw_82_);
lean_dec_ref(v_H_81_);
lean_dec_ref(v_inst_78_);
return v_res_94_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThClassPinsRec(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove(uint8_t builtin);
lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThClassPins(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_ThClassPinsRec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LocalToGlobal_ProjectiveLattices_FamilyUniformisationBasePointOrthogonalBis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
