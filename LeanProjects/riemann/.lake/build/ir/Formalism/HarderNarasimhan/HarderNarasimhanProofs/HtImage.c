// Lean compiler output
// Module: Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
// Imports: public import Init public meta import Init public import Formalism.HarderNarasimhan.StatementPl public import Formalism.HarderNarasimhan.DefsPl public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Complex_instNonUnitalCommRing;
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_Matrix_mulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HN_htImageCv___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_htImageCv___redArg___closed__0;
static lean_once_cell_t lp_tree_Formalism_HN_htImageCv___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_htImageCv___redArg___closed__1;
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_tree_Formalism_HN_htImageCv___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(2u);
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_nat_mod(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_tree_Formalism_HN_htImageCv___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_mod(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv___redArg(lean_object* v_y_7_, lean_object* v_v_8_, lean_object* v_i_9_){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_10_ = lean_obj_once(&lp_tree_Formalism_HN_htImageCv___redArg___closed__0, &lp_tree_Formalism_HN_htImageCv___redArg___closed__0_once, _init_lp_tree_Formalism_HN_htImageCv___redArg___closed__0);
lean_inc(v_i_9_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_i_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
lean_inc(v_v_8_);
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_v_8_);
lean_ctor_set(v___x_12_, 1, v___x_11_);
lean_inc(v_y_7_);
v___x_13_ = lean_apply_1(v_y_7_, v___x_12_);
v___x_14_ = lean_obj_once(&lp_tree_Formalism_HN_htImageCv___redArg___closed__1, &lp_tree_Formalism_HN_htImageCv___redArg___closed__1_once, _init_lp_tree_Formalism_HN_htImageCv___redArg___closed__1);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_i_9_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_v_8_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lean_apply_1(v_y_7_, v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_13_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv(lean_object* v_P_19_, lean_object* v_00_u03b9_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_y_23_, lean_object* v_v_24_, lean_object* v_i_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_tree_Formalism_HN_htImageCv___redArg(v_y_23_, v_v_24_, v_i_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageCv___boxed(lean_object* v_P_27_, lean_object* v_00_u03b9_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_y_31_, lean_object* v_v_32_, lean_object* v_i_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_tree_Formalism_HN_htImageCv(v_P_27_, v_00_u03b9_28_, v_inst_29_, v_inst_30_, v_y_31_, v_v_32_, v_i_33_);
lean_dec(v_inst_30_);
lean_dec(v_inst_29_);
return v_res_34_;
}
}
static lean_object* _init_lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lp_mathlib_Complex_instNonUnitalCommRing;
v___x_36_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg___lam__0(lean_object* v___x_37_, lean_object* v_M_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_snd_43_; lean_object* v_fst_44_; lean_object* v_fst_45_; lean_object* v_snd_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_snd_43_ = lean_ctor_get(v___y_42_, 1);
lean_inc(v_snd_43_);
v_fst_44_ = lean_ctor_get(v___y_42_, 0);
lean_inc(v_fst_44_);
lean_dec_ref(v___y_42_);
v_fst_45_ = lean_ctor_get(v_snd_43_, 0);
lean_inc(v_fst_45_);
v_snd_46_ = lean_ctor_get(v_snd_43_, 1);
lean_inc(v_snd_46_);
lean_dec(v_snd_43_);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_nat_mod(v___x_47_, v___x_37_);
v___x_49_ = lean_nat_dec_eq(v_snd_46_, v___x_48_);
lean_dec(v___x_48_);
lean_dec(v_snd_46_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v_im_54_; 
v___x_50_ = lean_obj_once(&lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0, &lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0);
lean_inc(v_fst_44_);
v___x_51_ = lean_apply_1(v_M_38_, v_fst_44_);
lean_inc(v_inst_40_);
v___x_52_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_htImageCv___boxed), 7, 6);
lean_closure_set(v___x_52_, 0, lean_box(0));
lean_closure_set(v___x_52_, 1, lean_box(0));
lean_closure_set(v___x_52_, 2, v_inst_39_);
lean_closure_set(v___x_52_, 3, v_inst_40_);
lean_closure_set(v___x_52_, 4, v_y_41_);
lean_closure_set(v___x_52_, 5, v_fst_44_);
v___x_53_ = lp_mathlib_Matrix_mulVec___redArg(v___x_50_, v_inst_40_, v___x_51_, v___x_52_, v_fst_45_);
v_im_54_ = lean_ctor_get(v___x_53_, 1);
lean_inc(v_im_54_);
lean_dec(v___x_53_);
return v_im_54_;
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_re_59_; 
v___x_55_ = lean_obj_once(&lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0, &lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0_once, _init_lp_tree_Formalism_HN_htImageMap___redArg___lam__0___closed__0);
lean_inc(v_fst_44_);
v___x_56_ = lean_apply_1(v_M_38_, v_fst_44_);
lean_inc(v_inst_40_);
v___x_57_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_htImageCv___boxed), 7, 6);
lean_closure_set(v___x_57_, 0, lean_box(0));
lean_closure_set(v___x_57_, 1, lean_box(0));
lean_closure_set(v___x_57_, 2, v_inst_39_);
lean_closure_set(v___x_57_, 3, v_inst_40_);
lean_closure_set(v___x_57_, 4, v_y_41_);
lean_closure_set(v___x_57_, 5, v_fst_44_);
v___x_58_ = lp_mathlib_Matrix_mulVec___redArg(v___x_55_, v_inst_40_, v___x_56_, v___x_57_, v_fst_45_);
v_re_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_re_59_);
lean_dec(v___x_58_);
return v_re_59_;
}
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg___lam__0___boxed(lean_object* v___x_60_, lean_object* v_M_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lp_tree_Formalism_HN_htImageMap___redArg___lam__0(v___x_60_, v_M_61_, v_inst_62_, v_inst_63_, v_y_64_, v___y_65_);
lean_dec(v___x_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_M_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___f_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___f_71_ = lean_alloc_closure((void*)(lp_tree_Formalism_HN_htImageMap___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_71_, 0, v___x_70_);
lean_closure_set(v___f_71_, 1, v_M_69_);
lean_closure_set(v___f_71_, 2, v_inst_67_);
lean_closure_set(v___f_71_, 3, v_inst_68_);
return v___f_71_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap(lean_object* v_P_72_, lean_object* v_00_u03b9_73_, lean_object* v_00_u03ba_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_M_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lp_tree_Formalism_HN_htImageMap___redArg(v_inst_75_, v_inst_76_, v_M_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_tree_Formalism_HN_htImageMap___boxed(lean_object* v_P_80_, lean_object* v_00_u03b9_81_, lean_object* v_00_u03ba_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_M_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = lp_tree_Formalism_HN_htImageMap(v_P_80_, v_00_u03b9_81_, v_00_u03ba_82_, v_inst_83_, v_inst_84_, v_inst_85_, v_M_86_);
lean_dec(v_inst_85_);
return v_res_87_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_StatementPl(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_DefsPl(uint8_t builtin);
lean_object* initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(uint8_t builtin);
lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_StatementPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_DefsPl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tree_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
