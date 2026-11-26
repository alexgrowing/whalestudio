// Lean compiler output
// Module: Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
// Imports: public import Init public meta import Init public import Lib.DiscreteSeries.Bessel.Basic public import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
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
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
lean_object* lp_mathlib_Complex_ofReal(lean_object*);
lean_object* lp_mathlib_Equiv_refl___redArg();
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqSum_decEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Matrix_submatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Matrix_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Multiset_disjSum___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___lam__0(lean_object*);
static const lean_closure_object lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0 = (const lean_object*)&lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0;
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0;
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__0 = (const lean_object*)&lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__1 = (const lean_object*)&lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___lam__0(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___closed__0 = (const lean_object*)&lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___closed__0 = (const lean_object*)&lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0 = (const lean_object*)&lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_RealPlace_eichlerMatrix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_RealPlace_eichlerMatrix___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_RealPlace_eichlerMatrix___closed__0 = (const lean_object*)&lp_GRH_New_RealPlace_eichlerMatrix___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___closed__0 = (const lean_object*)&lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerScalars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerScalars___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerScalars(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
lean_object* v_snd_5_; 
v_snd_5_ = lean_ctor_get(v_x_1_, 1);
if (lean_obj_tag(v_snd_5_) == 0)
{
lean_object* v_fst_6_; lean_object* v_val_7_; lean_object* v___x_8_; 
lean_inc_ref(v_snd_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_fst_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_6_);
lean_dec_ref(v_x_1_);
v_val_7_ = lean_ctor_get(v_snd_5_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v_snd_5_, 1);
v___x_8_ = lean_apply_2(v_h__1_2_, v_fst_6_, v_val_7_);
return v___x_8_;
}
else
{
lean_object* v_val_9_; 
lean_dec(v_h__1_2_);
v_val_9_ = lean_ctor_get(v_snd_5_, 0);
lean_inc(v_val_9_);
if (lean_obj_tag(v_val_9_) == 0)
{
lean_object* v_fst_10_; lean_object* v_val_11_; lean_object* v___x_12_; 
lean_dec(v_h__2_3_);
v_fst_10_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_10_);
lean_dec_ref(v_x_1_);
v_val_11_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_val_11_);
lean_dec_ref_known(v_val_9_, 1);
v___x_12_ = lean_apply_2(v_h__3_4_, v_fst_10_, v_val_11_);
return v___x_12_;
}
else
{
lean_object* v_fst_13_; lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__3_4_);
v_fst_13_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_13_);
lean_dec_ref(v_x_1_);
v_val_14_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_val_14_);
lean_dec_ref_known(v_val_9_, 1);
v___x_15_ = lean_apply_2(v_h__2_3_, v_fst_13_, v_val_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter(lean_object* v_00_U0001d530_16_, lean_object* v_motive_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_, lean_object* v_h__3_21_){
_start:
{
lean_object* v_snd_22_; 
v_snd_22_ = lean_ctor_get(v_x_18_, 1);
if (lean_obj_tag(v_snd_22_) == 0)
{
lean_object* v_fst_23_; lean_object* v_val_24_; lean_object* v___x_25_; 
lean_inc_ref(v_snd_22_);
lean_dec(v_h__3_21_);
lean_dec(v_h__2_20_);
v_fst_23_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_fst_23_);
lean_dec_ref(v_x_18_);
v_val_24_ = lean_ctor_get(v_snd_22_, 0);
lean_inc(v_val_24_);
lean_dec_ref_known(v_snd_22_, 1);
v___x_25_ = lean_apply_2(v_h__1_19_, v_fst_23_, v_val_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; 
lean_dec(v_h__1_19_);
v_val_26_ = lean_ctor_get(v_snd_22_, 0);
lean_inc(v_val_26_);
if (lean_obj_tag(v_val_26_) == 0)
{
lean_object* v_fst_27_; lean_object* v_val_28_; lean_object* v___x_29_; 
lean_dec(v_h__2_20_);
v_fst_27_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_fst_27_);
lean_dec_ref(v_x_18_);
v_val_28_ = lean_ctor_get(v_val_26_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_val_26_, 1);
v___x_29_ = lean_apply_2(v_h__3_21_, v_fst_27_, v_val_28_);
return v___x_29_;
}
else
{
lean_object* v_fst_30_; lean_object* v_val_31_; lean_object* v___x_32_; 
lean_dec(v_h__3_21_);
v_fst_30_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_fst_30_);
lean_dec_ref(v_x_18_);
v_val_31_ = lean_ctor_get(v_val_26_, 0);
lean_inc(v_val_31_);
lean_dec_ref_known(v_val_26_, 1);
v___x_32_ = lean_apply_2(v_h__2_20_, v_fst_30_, v_val_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter___boxed(lean_object* v_00_U0001d530_33_, lean_object* v_motive_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_, lean_object* v_h__3_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_GRH___private_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure_0__New_RealPlace_IsFreeEntry_match__1_splitter(v_00_U0001d530_33_, v_motive_34_, v_x_35_, v_h__1_36_, v_h__2_37_, v_h__3_38_);
lean_dec_ref(v_00_U0001d530_33_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___lam__0(lean_object* v_z_40_){
_start:
{
lean_object* v_re_41_; lean_object* v_im_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
v_re_41_ = lean_ctor_get(v_z_40_, 0);
v_im_42_ = lean_ctor_get(v_z_40_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_z_40_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v_z_40_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_im_42_);
lean_inc(v_re_41_);
lean_dec(v_z_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___f_46_; lean_object* v___x_48_; 
v___f_46_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_46_, 0, v_im_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___f_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_re_41_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___f_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg(lean_object* v_M_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___f_55_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0));
v___x_56_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_56_, 0, lean_box(0));
lean_closure_set(v___x_56_, 1, lean_box(0));
lean_closure_set(v___x_56_, 2, lean_box(0));
lean_closure_set(v___x_56_, 3, v_M_52_);
v___x_57_ = lp_mathlib_Matrix_map___redArg(v___x_56_, v___f_55_, v_a_53_, v_a_54_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3(lean_object* v_m_58_, lean_object* v_n_59_, lean_object* v_M_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg(v_M_60_, v_a_61_, v_a_62_);
return v___x_63_;
}
}
LEAN_EXPORT uint8_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0(lean_object* v_00_U0001d530_64_, lean_object* v_a_65_, lean_object* v_b_66_){
_start:
{
lean_object* v_decEqIndex_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_decEqIndex_67_ = lean_ctor_get(v_00_U0001d530_64_, 2);
lean_inc_ref(v_decEqIndex_67_);
lean_dec_ref(v_00_U0001d530_64_);
v___x_68_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___x_69_ = l_instDecidableEqSum_decEq___redArg(v_decEqIndex_67_, v___x_68_, v_a_65_, v_b_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0___boxed(lean_object* v_00_U0001d530_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0(v_00_U0001d530_70_, v_a_71_, v_b_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1(lean_object* v___f_75_, lean_object* v___x_76_, lean_object* v_a_77_, lean_object* v_b_78_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = l_instDecidableEqSum_decEq___redArg(v___f_75_, v___x_76_, v_a_77_, v_b_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1___boxed(lean_object* v___f_80_, lean_object* v___x_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1(v___f_80_, v___x_81_, v_a_82_, v_b_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
static lean_object* _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_87_ = lp_mathlib_Complex_ofReal(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2(lean_object* v_00_U0001d530_88_, lean_object* v___f_89_, lean_object* v_d_90_, lean_object* v_i_91_, lean_object* v_j_92_){
_start:
{
lean_object* v_00_u03f1_93_; lean_object* v___x_94_; lean_object* v___f_95_; uint8_t v___x_96_; 
v_00_u03f1_93_ = lean_ctor_get(v_00_U0001d530_88_, 0);
lean_inc(v_00_u03f1_93_);
lean_dec_ref(v_00_U0001d530_88_);
v___x_94_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_94_, 0, v_00_u03f1_93_);
lean_inc_ref(v___x_94_);
v___f_95_ = lean_alloc_closure((void*)(lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__1___boxed), 4, 2);
lean_closure_set(v___f_95_, 0, v___f_89_);
lean_closure_set(v___f_95_, 1, v___x_94_);
lean_inc_ref(v_i_91_);
v___x_96_ = l_instDecidableEqSum_decEq___redArg(v___x_94_, v___f_95_, v_i_91_, v_j_92_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v_i_91_);
lean_dec_ref(v_d_90_);
v___x_97_ = lean_obj_once(&lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0, &lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0_once, _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_1(v_d_90_, v_i_91_);
return v___x_98_;
}
}
}
static lean_object* _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_mathlib_Equiv_refl___redArg();
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4(lean_object* v_00_U0001d530_100_, lean_object* v_d_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v___x_104_; lean_object* v_toFun_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___x_104_ = lean_obj_once(&lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0, &lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0_once, _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___closed__0);
v_toFun_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc_ref(v_00_U0001d530_100_);
v___f_106_ = lean_alloc_closure((void*)(lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__0___boxed), 3, 1);
lean_closure_set(v___f_106_, 0, v_00_U0001d530_100_);
v___f_107_ = lean_alloc_closure((void*)(lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2), 5, 3);
lean_closure_set(v___f_107_, 0, v_00_U0001d530_100_);
lean_closure_set(v___f_107_, 1, v___f_106_);
lean_closure_set(v___f_107_, 2, v_d_101_);
lean_inc(v_toFun_105_);
v___x_108_ = lean_apply_3(v_toFun_105_, v___f_107_, v_a_102_, v_a_103_);
return v___x_108_;
}
}
static lean_object* _init_lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_6358291____hygCtx___hyg_2_;
v___x_110_ = lp_mathlib_Complex_ofReal(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0(lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0, &lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0_once, _init_lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___closed__0);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0___boxed(lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__0(v_x_113_);
lean_dec_ref(v_x_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__1(lean_object* v_00_U0001d530_115_, lean_object* v___f_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4(v_00_U0001d530_115_, v___f_116_, v___y_117_, v___y_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2(lean_object* v___y_120_){
_start:
{
lean_inc_ref(v___y_120_);
return v___y_120_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2___boxed(lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__2(v___y_121_);
lean_dec_ref(v___y_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(lean_object* v_00_U0001d530_125_, lean_object* v_u_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v___f_129_ = ((lean_object*)(lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__0));
v___f_130_ = lean_alloc_closure((void*)(lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___lam__1), 4, 2);
lean_closure_set(v___f_130_, 0, v_00_U0001d530_125_);
lean_closure_set(v___f_130_, 1, v___f_129_);
v___f_131_ = ((lean_object*)(lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__1));
v___x_132_ = lp_mathlib_Matrix_submatrix___redArg(v___f_130_, v___f_131_, v_u_126_, v_a_127_, v_a_128_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0(lean_object* v_00_U0001d530_133_, lean_object* v_m_134_, lean_object* v_u_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_133_, v_u_135_, v_a_136_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1___lam__0(lean_object* v_v_139_, lean_object* v_w_140_, lean_object* v_i_141_){
_start:
{
lean_object* v___x_142_; lean_object* v_re_143_; lean_object* v_im_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_inc(v_i_141_);
v___x_142_ = lean_apply_1(v_v_139_, v_i_141_);
v_re_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_re_143_);
v_im_144_ = lean_ctor_get(v___x_142_, 1);
lean_inc(v_im_144_);
lean_dec_ref(v___x_142_);
v___x_145_ = lean_apply_1(v_w_140_, v_i_141_);
v___x_146_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_143_, v_im_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___lam__0(lean_object* v_x1_147_, lean_object* v_x2_148_){
_start:
{
lean_object* v_re_149_; lean_object* v_im_150_; lean_object* v_re_151_; lean_object* v_im_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_161_; 
v_re_149_ = lean_ctor_get(v_x1_147_, 0);
lean_inc(v_re_149_);
v_im_150_ = lean_ctor_get(v_x1_147_, 1);
lean_inc(v_im_150_);
lean_dec_ref(v_x1_147_);
v_re_151_ = lean_ctor_get(v_x2_148_, 0);
v_im_152_ = lean_ctor_get(v_x2_148_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x2_148_);
if (v_isSharedCheck_161_ == 0)
{
v___x_154_ = v_x2_148_;
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_im_152_);
lean_inc(v_re_151_);
lean_dec(v_x2_148_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_161_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___x_159_; 
v___f_156_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_156_, 0, v_re_149_);
lean_closure_set(v___f_156_, 1, v_re_151_);
v___f_157_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_157_, 0, v_im_150_);
lean_closure_set(v___f_157_, 1, v_im_152_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___f_157_);
lean_ctor_set(v___x_154_, 0, v___f_156_);
v___x_159_ = v___x_154_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___f_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___f_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3(lean_object* v_s_163_){
_start:
{
lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___f_164_ = ((lean_object*)(lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3___closed__0));
v___x_165_ = lean_obj_once(&lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0, &lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0_once, _init_lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4___lam__2___closed__0);
v___x_166_ = l_List_foldrTR___redArg(v___f_164_, v___x_165_, v_s_163_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(lean_object* v_s_167_, lean_object* v_f_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lp_mathlib_Multiset_map___redArg(v_f_168_, v_s_167_);
v___x_170_ = lp_GRH_Multiset_sum___at___00Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1_spec__3(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1(lean_object* v_00_U0001d530_171_, lean_object* v_v_172_, lean_object* v_w_173_){
_start:
{
lean_object* v_fintypeIndex_174_; lean_object* v___f_175_; lean_object* v___x_176_; 
v_fintypeIndex_174_ = lean_ctor_get(v_00_U0001d530_171_, 1);
lean_inc(v_fintypeIndex_174_);
lean_dec_ref(v_00_U0001d530_171_);
v___f_175_ = lean_alloc_closure((void*)(lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_175_, 0, v_v_172_);
lean_closure_set(v___f_175_, 1, v_w_173_);
v___x_176_ = lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(v_fintypeIndex_174_, v___f_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2___lam__0(lean_object* v_v_177_, lean_object* v_w_178_, lean_object* v_i_179_){
_start:
{
lean_object* v___x_180_; lean_object* v_re_181_; lean_object* v_im_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v_i_179_);
v___x_180_ = lean_apply_1(v_v_177_, v_i_179_);
v_re_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_re_181_);
v_im_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_im_182_);
lean_dec_ref(v___x_180_);
v___x_183_ = lean_apply_1(v_w_178_, v_i_179_);
v___x_184_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_181_, v_im_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(lean_object* v___x_185_, lean_object* v_v_186_, lean_object* v_w_187_){
_start:
{
lean_object* v___f_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___f_188_ = lean_alloc_closure((void*)(lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_188_, 0, v_v_186_);
lean_closure_set(v___f_188_, 1, v_w_187_);
v___x_189_ = l_List_finRange(v___x_185_);
v___x_190_ = lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(v___x_189_, v___f_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__0(lean_object* v___y_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___y_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__1(lean_object* v_00_U0001d530_195_, lean_object* v___f_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_195_, v___f_196_, v___y_197_, v___y_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6(lean_object* v_00_U0001d530_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___f_204_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___closed__0));
v___f_205_ = lean_alloc_closure((void*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___lam__1), 4, 2);
lean_closure_set(v___f_205_, 0, v_00_U0001d530_201_);
lean_closure_set(v___f_205_, 1, v___f_204_);
v___f_206_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0));
v___x_207_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_207_, 0, lean_box(0));
lean_closure_set(v___x_207_, 1, lean_box(0));
lean_closure_set(v___x_207_, 2, lean_box(0));
lean_closure_set(v___x_207_, 3, v___f_205_);
v___x_208_ = lp_mathlib_Matrix_map___redArg(v___x_207_, v___f_206_, v_a_202_, v_a_203_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__0(lean_object* v___y_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___y_209_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__1(lean_object* v_00_U0001d530_212_, lean_object* v___f_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_212_, v___f_213_, v___y_214_, v___y_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7(lean_object* v_00_U0001d530_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___f_221_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0));
v___f_222_ = lean_alloc_closure((void*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__1), 4, 2);
lean_closure_set(v___f_222_, 0, v_00_U0001d530_218_);
lean_closure_set(v___f_222_, 1, v___f_221_);
v___f_223_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0));
v___x_224_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, lean_box(0));
lean_closure_set(v___x_224_, 2, lean_box(0));
lean_closure_set(v___x_224_, 3, v___f_222_);
v___x_225_ = lp_mathlib_Matrix_map___redArg(v___x_224_, v___f_223_, v_a_219_, v_a_220_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__1(lean_object* v_00_U0001d530_226_, lean_object* v_a_227_, lean_object* v_j_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6(v_00_U0001d530_226_, v_j_228_, v_a_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__0(lean_object* v_val_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v_val_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__2(lean_object* v_00_U0001d530_232_, lean_object* v___f_233_, lean_object* v_a_234_, lean_object* v_j_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_232_, v___f_233_, v_a_234_, v_j_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__3(lean_object* v_00_u03c9_237_, lean_object* v_j_238_, lean_object* v_j_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg(v_00_u03c9_237_, v_j_239_, v_j_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__4(lean_object* v_00_u03c9_241_, lean_object* v_00_u03f1_242_, lean_object* v___f_243_, lean_object* v_j_244_){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; 
v___f_245_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__3), 3, 2);
lean_closure_set(v___f_245_, 0, v_00_u03c9_241_);
lean_closure_set(v___f_245_, 1, v_j_244_);
v___x_246_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(v_00_u03f1_242_, v___f_243_, v___f_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__5(lean_object* v_00_U0001d530_247_, lean_object* v_a_248_, lean_object* v_j_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7(v_00_U0001d530_247_, v_j_249_, v_a_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__7(lean_object* v_00_U0001d530_251_, lean_object* v___f_252_, lean_object* v_a_253_, lean_object* v_j_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_251_, v___f_252_, v_a_253_, v_j_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__6(lean_object* v_00_u03c9_256_, lean_object* v_j_257_, lean_object* v_j_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = lean_apply_2(v_00_u03c9_256_, v_j_258_, v_j_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__8(lean_object* v_00_u03c9_260_, lean_object* v_00_U0001d530_261_, lean_object* v___f_262_, lean_object* v_j_263_){
_start:
{
lean_object* v___f_264_; lean_object* v___x_265_; 
v___f_264_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__6), 3, 2);
lean_closure_set(v___f_264_, 0, v_00_u03c9_260_);
lean_closure_set(v___f_264_, 1, v_j_263_);
v___x_265_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1(v_00_U0001d530_261_, v___f_262_, v___f_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__12(lean_object* v_00_u03bc_266_, lean_object* v_j_267_, lean_object* v_j_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_apply_2(v_00_u03bc_266_, v_j_268_, v_j_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix___lam__9(lean_object* v_00_u03bc_270_, lean_object* v_00_u03f1_271_, lean_object* v___f_272_, lean_object* v_j_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; 
v___f_274_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__12), 3, 2);
lean_closure_set(v___f_274_, 0, v_00_u03bc_270_);
lean_closure_set(v___f_274_, 1, v_j_273_);
v___x_275_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(v_00_u03f1_271_, v___f_272_, v___f_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerMatrix(lean_object* v_00_U0001d530_277_, lean_object* v_00_u03c9_278_, lean_object* v_00_u03bc_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_00_u03f1_282_; lean_object* v___f_283_; lean_object* v___x_284_; lean_object* v_re_285_; lean_object* v_im_286_; lean_object* v___f_287_; lean_object* v___f_288_; lean_object* v___f_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v_re_292_; lean_object* v_im_293_; lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v_re_299_; lean_object* v_im_300_; lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v_re_303_; lean_object* v_im_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_321_; 
v_00_u03f1_282_ = lean_ctor_get(v_00_U0001d530_277_, 0);
lean_inc_n(v_00_u03f1_282_, 4);
v___f_283_ = ((lean_object*)(lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg___closed__0));
lean_inc_ref_n(v_a_281_, 2);
lean_inc_ref_n(v_a_280_, 2);
lean_inc_ref_n(v_00_U0001d530_277_, 6);
v___x_284_ = lp_GRH_Matrix_diagonal___at___00New_RealPlace_eichlerMatrix_spec__4(v_00_U0001d530_277_, v___f_283_, v_a_280_, v_a_281_);
v_re_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_re_285_);
v_im_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc(v_im_286_);
lean_dec_ref(v___x_284_);
v___f_287_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__1), 3, 2);
lean_closure_set(v___f_287_, 0, v_00_U0001d530_277_);
lean_closure_set(v___f_287_, 1, v_a_281_);
v___f_288_ = ((lean_object*)(lp_GRH_New_RealPlace_eichlerMatrix___closed__0));
v___f_289_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__2), 4, 3);
lean_closure_set(v___f_289_, 0, v_00_U0001d530_277_);
lean_closure_set(v___f_289_, 1, v___f_288_);
lean_closure_set(v___f_289_, 2, v_a_280_);
lean_inc_ref(v___f_289_);
lean_inc_ref(v_00_u03c9_278_);
v___f_290_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__4), 4, 3);
lean_closure_set(v___f_290_, 0, v_00_u03c9_278_);
lean_closure_set(v___f_290_, 1, v_00_u03f1_282_);
lean_closure_set(v___f_290_, 2, v___f_289_);
v___x_291_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1(v_00_U0001d530_277_, v___f_290_, v___f_287_);
v_re_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_re_292_);
v_im_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc(v_im_293_);
lean_dec_ref(v___x_291_);
v___f_294_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__5), 3, 2);
lean_closure_set(v___f_294_, 0, v_00_U0001d530_277_);
lean_closure_set(v___f_294_, 1, v_a_281_);
v___f_295_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6___closed__0));
v___f_296_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__7), 4, 3);
lean_closure_set(v___f_296_, 0, v_00_U0001d530_277_);
lean_closure_set(v___f_296_, 1, v___f_295_);
lean_closure_set(v___f_296_, 2, v_a_280_);
v___f_297_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__8), 4, 3);
lean_closure_set(v___f_297_, 0, v_00_u03c9_278_);
lean_closure_set(v___f_297_, 1, v_00_U0001d530_277_);
lean_closure_set(v___f_297_, 2, v___f_296_);
lean_inc_ref(v___f_294_);
v___x_298_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(v_00_u03f1_282_, v___f_297_, v___f_294_);
v_re_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_re_299_);
v_im_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_im_300_);
lean_dec_ref(v___x_298_);
v___f_301_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerMatrix___lam__9), 4, 3);
lean_closure_set(v___f_301_, 0, v_00_u03bc_279_);
lean_closure_set(v___f_301_, 1, v_00_u03f1_282_);
lean_closure_set(v___f_301_, 2, v___f_289_);
v___x_302_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerMatrix_spec__2(v_00_u03f1_282_, v___f_301_, v___f_294_);
v_re_303_ = lean_ctor_get(v___x_302_, 0);
v_im_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_321_ == 0)
{
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_321_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_im_304_);
lean_inc(v_re_303_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_321_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_319_; 
v___f_308_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_308_, 0, v_re_285_);
lean_closure_set(v___f_308_, 1, v_re_292_);
v___f_309_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_309_, 0, v_im_286_);
lean_closure_set(v___f_309_, 1, v_im_293_);
v___f_310_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_310_, 0, v_re_299_);
v___f_311_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_311_, 0, v___f_308_);
lean_closure_set(v___f_311_, 1, v___f_310_);
v___f_312_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_312_, 0, v_im_300_);
v___f_313_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_313_, 0, v___f_309_);
lean_closure_set(v___f_313_, 1, v___f_312_);
v___f_314_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_314_, 0, v_re_303_);
v___f_315_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_315_, 0, v___f_311_);
lean_closure_set(v___f_315_, 1, v___f_314_);
v___f_316_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_316_, 0, v_im_304_);
v___f_317_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_317_, 0, v___f_313_);
lean_closure_set(v___f_317_, 1, v___f_316_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___f_317_);
lean_ctor_set(v___x_306_, 0, v___f_315_);
v___x_319_ = v___x_306_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___f_315_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___f_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1(lean_object* v_00_u03b9_322_, lean_object* v_s_323_, lean_object* v_f_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(v_s_323_, v_f_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___lam__0(lean_object* v_v_326_, lean_object* v_w_327_, lean_object* v_i_328_){
_start:
{
lean_object* v___x_329_; lean_object* v_re_330_; lean_object* v_im_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_inc_ref(v_i_328_);
v___x_329_ = lean_apply_1(v_v_326_, v_i_328_);
v_re_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_re_330_);
v_im_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc(v_im_331_);
lean_dec_ref(v___x_329_);
v___x_332_ = lean_apply_1(v_w_327_, v_i_328_);
v___x_333_ = lp_mathlib_Complex_mulAux___at___00Zsqrtd_lift___at___00GaussianInt_toComplex_spec__0_spec__1(v_re_330_, v_im_331_, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0(lean_object* v___x_337_, lean_object* v_00_U0001d530_338_, lean_object* v_v_339_, lean_object* v_w_340_){
_start:
{
lean_object* v_fintypeIndex_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_fintypeIndex_341_ = lean_ctor_get(v_00_U0001d530_338_, 1);
lean_inc(v_fintypeIndex_341_);
lean_dec_ref(v_00_U0001d530_338_);
v___f_342_ = lean_alloc_closure((void*)(lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_342_, 0, v_v_339_);
lean_closure_set(v___f_342_, 1, v_w_340_);
v___x_343_ = l_List_finRange(v___x_337_);
v___x_344_ = ((lean_object*)(lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0___closed__0));
v___x_345_ = lp_mathlib_Multiset_disjSum___redArg(v_fintypeIndex_341_, v___x_344_);
lean_inc(v___x_343_);
v___x_346_ = lp_mathlib_Multiset_disjSum___redArg(v___x_345_, v___x_343_);
v___x_347_ = lp_mathlib_Multiset_disjSum___redArg(v___x_343_, v___x_346_);
v___x_348_ = lp_GRH_Finset_sum___at___00dotProduct___at___00New_RealPlace_eichlerMatrix_spec__1_spec__1___redArg(v___x_347_, v___f_342_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__0(lean_object* v_00_U0001d530_349_, lean_object* v_a_350_, lean_object* v_j_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__6(v_00_U0001d530_349_, v_a_350_, v_j_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__2(lean_object* v_00_U0001d530_353_, lean_object* v___f_354_, lean_object* v_a_355_, lean_object* v_j_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = lp_GRH_New_inclMatrix___at___00New_RealPlace_eichlerMatrix_spec__0___redArg(v_00_U0001d530_353_, v___f_354_, v_j_356_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__1(lean_object* v_val_358_, lean_object* v_j_359_, lean_object* v_j_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_2(v_val_358_, v_j_360_, v_j_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors___lam__3(lean_object* v_val_362_, lean_object* v_00_u03f1_363_, lean_object* v_00_U0001d530_364_, lean_object* v___f_365_, lean_object* v_j_366_){
_start:
{
lean_object* v___f_367_; lean_object* v___x_368_; 
v___f_367_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__1), 3, 2);
lean_closure_set(v___f_367_, 0, v_val_362_);
lean_closure_set(v___f_367_, 1, v_j_366_);
v___x_368_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0(v_00_u03f1_363_, v_00_U0001d530_364_, v___f_365_, v___f_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerVectors(lean_object* v_00_U0001d530_369_, lean_object* v_u_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_00_u03f1_373_; lean_object* v_val_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v_re_380_; lean_object* v_im_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_390_; 
v_00_u03f1_373_ = lean_ctor_get(v_00_U0001d530_369_, 0);
lean_inc_n(v_00_u03f1_373_, 2);
v_val_374_ = lean_ctor_get(v_u_370_, 0);
lean_inc(v_val_374_);
lean_dec_ref(v_u_370_);
lean_inc_ref_n(v_00_U0001d530_369_, 3);
v___f_375_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__0), 3, 2);
lean_closure_set(v___f_375_, 0, v_00_U0001d530_369_);
lean_closure_set(v___f_375_, 1, v_a_371_);
v___f_376_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0));
v___f_377_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__2), 4, 3);
lean_closure_set(v___f_377_, 0, v_00_U0001d530_369_);
lean_closure_set(v___f_377_, 1, v___f_376_);
lean_closure_set(v___f_377_, 2, v_a_372_);
v___f_378_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__3), 5, 4);
lean_closure_set(v___f_378_, 0, v_val_374_);
lean_closure_set(v___f_378_, 1, v_00_u03f1_373_);
lean_closure_set(v___f_378_, 2, v_00_U0001d530_369_);
lean_closure_set(v___f_378_, 3, v___f_375_);
v___x_379_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0(v_00_u03f1_373_, v_00_U0001d530_369_, v___f_378_, v___f_377_);
v_re_380_ = lean_ctor_get(v___x_379_, 0);
v_im_381_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_390_ == 0)
{
v___x_383_ = v___x_379_;
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_im_381_);
lean_inc(v_re_380_);
lean_dec(v___x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_390_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___x_388_; 
v___f_385_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_385_, 0, v_re_380_);
v___f_386_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_386_, 0, v_im_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___f_386_);
lean_ctor_set(v___x_383_, 0, v___f_385_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___f_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___f_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerScalars_spec__0(lean_object* v_00_U0001d530_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___f_394_ = ((lean_object*)(lp_GRH_New_RealPlace_eichlerMatrix___closed__0));
v___f_395_ = lean_alloc_closure((void*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___lam__1), 4, 2);
lean_closure_set(v___f_395_, 0, v_00_U0001d530_391_);
lean_closure_set(v___f_395_, 1, v___f_394_);
v___f_396_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___redArg___closed__0));
v___x_397_ = lean_alloc_closure((void*)(lp_mathlib_Matrix_transpose), 6, 4);
lean_closure_set(v___x_397_, 0, lean_box(0));
lean_closure_set(v___x_397_, 1, lean_box(0));
lean_closure_set(v___x_397_, 2, lean_box(0));
lean_closure_set(v___x_397_, 3, v___f_395_);
v___x_398_ = lp_mathlib_Matrix_map___redArg(v___x_397_, v___f_396_, v_a_392_, v_a_393_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerScalars___lam__0(lean_object* v_00_U0001d530_399_, lean_object* v_a_400_, lean_object* v_j_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerScalars_spec__0(v_00_U0001d530_399_, v_a_400_, v_j_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_RealPlace_eichlerScalars(lean_object* v_00_U0001d530_403_, lean_object* v_u_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_00_u03f1_407_; lean_object* v_val_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v_re_414_; lean_object* v_im_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
v_00_u03f1_407_ = lean_ctor_get(v_00_U0001d530_403_, 0);
lean_inc_n(v_00_u03f1_407_, 2);
v_val_408_ = lean_ctor_get(v_u_404_, 0);
lean_inc(v_val_408_);
lean_dec_ref(v_u_404_);
lean_inc_ref_n(v_00_U0001d530_403_, 3);
v___f_409_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerScalars___lam__0), 3, 2);
lean_closure_set(v___f_409_, 0, v_00_U0001d530_403_);
lean_closure_set(v___f_409_, 1, v_a_405_);
v___f_410_ = ((lean_object*)(lp_GRH_Matrix_conjTranspose___at___00New_RealPlace_eichlerMatrix_spec__3___at___00New_RealPlace_eichlerMatrix_spec__7___closed__0));
v___f_411_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__2), 4, 3);
lean_closure_set(v___f_411_, 0, v_00_U0001d530_403_);
lean_closure_set(v___f_411_, 1, v___f_410_);
lean_closure_set(v___f_411_, 2, v_a_406_);
v___f_412_ = lean_alloc_closure((void*)(lp_GRH_New_RealPlace_eichlerVectors___lam__3), 5, 4);
lean_closure_set(v___f_412_, 0, v_val_408_);
lean_closure_set(v___f_412_, 1, v_00_u03f1_407_);
lean_closure_set(v___f_412_, 2, v_00_U0001d530_403_);
lean_closure_set(v___f_412_, 3, v___f_409_);
v___x_413_ = lp_GRH_dotProduct___at___00New_RealPlace_eichlerVectors_spec__0(v_00_u03f1_407_, v_00_U0001d530_403_, v___f_412_, v___f_411_);
v_re_414_ = lean_ctor_get(v___x_413_, 0);
v_im_415_ = lean_ctor_get(v___x_413_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_424_ == 0)
{
v___x_417_ = v___x_413_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_im_415_);
lean_inc(v_re_414_);
lean_dec(v___x_413_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___x_422_; 
v___f_419_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_419_, 0, v_re_414_);
v___f_420_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_420_, 0, v_im_415_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v___f_420_);
lean_ctor_set(v___x_417_, 0, v___f_419_);
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___f_419_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___f_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_Basic(uint8_t builtin);
lean_object* initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_RightDerivatives(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_DiscreteSeries_Bessel_UnipotentHaarMeasure(uint8_t builtin) {
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
res = initialize_GRH_Lib_DiscreteSeries_Bessel_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_DiscreteSeries_FlenstedJensen_RightDerivatives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
