// Lean compiler output
// Module: Lib.Cohomology.TorsionTheories
// Imports: public import Init public meta import Init public import Lib.Adelic.Unitary.Defs public import Lib.Cohomology.Etale.RelativeChains public import Lib.Cohomology.LerayHirsch public import Lib.General.Algebra.CohomologyBaseChange public import Lib.PadicComparison.HodgeTate.ExtCocycles
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
lean_object* lp_mathlib_CategoryTheory_Functor_Elements_00_u03c0___redArg();
lean_object* lp_mathlib_ZMod_instField___redArg(lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_id___redArg();
lean_object* lp_mathlib_CategoryTheory_ObjectProperty_00_u03b9___redArg();
lean_object* lp_mathlib_CategoryTheory_Functor_comp___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_ObjectProperty_lift___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* lp_GRH_New_Variety_locConstCoeff(lean_object*);
lean_object* lp_mathlib_CategoryTheory_Functor_sectionsEquivHom___redArg(lean_object*);
extern lean_object* lp_mathlib_CategoryTheory_types;
lean_object* lp_mathlib_CategoryTheory_Functor_const___redArg(lean_object*);
lean_object* lp_mathlib_TensorProduct_mk___redArg();
lean_object* lp_mathlib_FreeAbelianGroup_of___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_flip___redArg(lean_object*);
lean_object* lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0(lean_object*, lean_object*);
lean_object* lp_mathlib_QuotientAddGroup_Quotient_addGroup___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_QuotientAddGroup_map___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_freeAb_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_AddCommGrpCat_instCategory;
lean_object* lp_GRH_New_Variety_freeAb___redArg();
lean_object* lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_GRH_New_Variety_abCoker_desc___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_onePointFunctor___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_onePointFunctor___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0;
static lean_once_cell_t lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_sectionMap___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_sectionMap___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_elementsProj___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_elementsProj___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object lp_GRH_New_Variety_tautologicalSection___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_tautologicalSection___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_tautologicalSection___redArg___closed__0_value;
static lean_once_cell_t lp_GRH_New_Variety_tautologicalSection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___closed__1;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_tautologicalSection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_tautologicalSection___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_TestOver_toTest___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__0_value;
static const lean_closure_object lp_GRH_New_Variety_TestOver_toTest___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__1 = (const lean_object*)&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__1_value;
static lean_once_cell_t lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2;
static const lean_ctor_object lp_GRH_New_Variety_TestOver_toTest___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__0_value),((lean_object*)&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__1_value)}};
static const lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__3 = (const lean_object*)&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__3_value;
static lean_once_cell_t lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4;
static lean_once_cell_t lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___boxed(lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_TestOver_toTest___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_TestOver_toTest___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_ringOf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_ringOf___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0 = (const lean_object*)&lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0_value;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg();
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Variety_onePointFunctor___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lp_mathlib_CategoryTheory_types;
v___x_2_ = lp_mathlib_CategoryTheory_Functor_const___redArg(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___redArg(){
_start:
{
lean_object* v___x_4_; lean_object* v_obj_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&lp_GRH_New_Variety_onePointFunctor___redArg___closed__0, &lp_GRH_New_Variety_onePointFunctor___redArg___closed__0_once, _init_lp_GRH_New_Variety_onePointFunctor___redArg___closed__0);
v_obj_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_obj_5_);
v___x_6_ = lean_apply_1(v_obj_5_, lean_box(0));
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___redArg___boxed(lean_object* v___dummy_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_GRH_New_Variety_onePointFunctor___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor(lean_object* v_C_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___x_11_; lean_object* v_obj_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&lp_GRH_New_Variety_onePointFunctor___redArg___closed__0, &lp_GRH_New_Variety_onePointFunctor___redArg___closed__0_once, _init_lp_GRH_New_Variety_onePointFunctor___redArg___closed__0);
v_obj_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_obj_12_);
v___x_13_ = lean_apply_1(v_obj_12_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_onePointFunctor___boxed(lean_object* v_C_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_GRH_New_Variety_onePointFunctor(v_C_14_, v_inst_15_);
lean_dec_ref(v_inst_15_);
return v_res_16_;
}
}
static lean_object* _init_lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_mathlib_TensorProduct_mk___redArg();
return v___x_17_;
}
}
static lean_object* _init_lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(0);
v___x_19_ = lp_mathlib_FreeAbelianGroup_of___redArg(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0(lean_object* v_00_u03c1_20_, lean_object* v_S_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_180__overap_26_; lean_object* v___x_27_; lean_object* v___f_28_; 
v___x_23_ = lean_obj_once(&lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0, &lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0_once, _init_lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__0);
v___x_24_ = lean_obj_once(&lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1, &lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1_once, _init_lp_GRH_New_Variety_tensorPoint___redArg___lam__0___closed__1);
v___x_25_ = lean_apply_2(v_00_u03c1_20_, v___y_22_, v___x_24_);
v___x_180__overap_26_ = lp_mathlib_LinearMap_flip___redArg(v___x_23_);
v___x_27_ = lean_apply_1(v___x_180__overap_26_, v___x_25_);
v___f_28_ = lean_alloc_closure((void*)(lp_mathlib_LinearMap_toAddMonoidHom___redArg___lam__0), 2, 1);
lean_closure_set(v___f_28_, 0, v___x_27_);
return v___f_28_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg___lam__0___boxed(lean_object* v_00_u03c1_29_, lean_object* v_S_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = lp_GRH_New_Variety_tensorPoint___redArg___lam__0(v_00_u03c1_29_, v_S_30_, v___y_31_);
lean_dec_ref(v_S_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___redArg(lean_object* v_00_u03c1_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_tensorPoint___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_34_, 0, v_00_u03c1_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint(lean_object* v_C_35_, lean_object* v_inst_36_, lean_object* v_K_37_, lean_object* v_00_u03c1_38_){
_start:
{
lean_object* v___f_39_; 
v___f_39_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_tensorPoint___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_39_, 0, v_00_u03c1_38_);
return v___f_39_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tensorPoint___boxed(lean_object* v_C_40_, lean_object* v_inst_41_, lean_object* v_K_42_, lean_object* v_00_u03c1_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_GRH_New_Variety_tensorPoint(v_C_40_, v_inst_41_, v_K_42_, v_00_u03c1_43_);
lean_dec_ref(v_K_42_);
lean_dec_ref(v_inst_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg___lam__0(lean_object* v_00_u03c6_45_, lean_object* v_q_46_, lean_object* v_c_47_){
_start:
{
lean_object* v_obj_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_57_; 
v_obj_48_ = lean_ctor_get(v_00_u03c6_45_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v_00_u03c6_45_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_00_u03c6_45_, 1);
lean_dec(v_unused_58_);
v___x_50_ = v_00_u03c6_45_;
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_obj_48_);
lean_dec(v_00_u03c6_45_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
lean_inc(v_c_47_);
v___x_52_ = lean_apply_1(v_obj_48_, v_c_47_);
v___x_53_ = lean_apply_1(v_q_46_, v_c_47_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v___x_53_);
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg___lam__1(lean_object* v_00_u03c6_59_, lean_object* v_X_60_, lean_object* v_Y_61_, lean_object* v_f_62_){
_start:
{
lean_object* v_map_63_; lean_object* v___x_64_; 
v_map_63_ = lean_ctor_get(v_00_u03c6_59_, 1);
lean_inc(v_map_63_);
lean_dec_ref(v_00_u03c6_59_);
v___x_64_ = lean_apply_3(v_map_63_, v_X_60_, v_Y_61_, v_f_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___redArg(lean_object* v_00_u03c6_65_, lean_object* v_q_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_69_; 
lean_inc_ref(v_00_u03c6_65_);
v___f_67_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_sectionLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_67_, 0, v_00_u03c6_65_);
lean_closure_set(v___f_67_, 1, v_q_66_);
v___f_68_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_sectionLift___redArg___lam__1), 4, 1);
lean_closure_set(v___f_68_, 0, v_00_u03c6_65_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___f_67_);
lean_ctor_set(v___x_69_, 1, v___f_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift(lean_object* v_C_70_, lean_object* v_C_x27_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_X_74_, lean_object* v_00_u03c6_75_, lean_object* v_q_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_GRH_New_Variety_sectionLift___redArg(v_00_u03c6_75_, v_q_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionLift___boxed(lean_object* v_C_78_, lean_object* v_C_x27_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_X_82_, lean_object* v_00_u03c6_83_, lean_object* v_q_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = lp_GRH_New_Variety_sectionLift(v_C_78_, v_C_x27_79_, v_inst_80_, v_inst_81_, v_X_82_, v_00_u03c6_83_, v_q_84_);
lean_dec_ref(v_X_82_);
lean_dec_ref(v_inst_81_);
lean_dec_ref(v_inst_80_);
return v_res_85_;
}
}
static lean_object* _init_lp_GRH_New_Variety_sectionMap___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_box(0);
v___x_87_ = lp_mathlib_CategoryTheory_Functor_sectionsEquivHom___redArg(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap___redArg(lean_object* v_q_88_){
_start:
{
lean_object* v___x_89_; lean_object* v_toFun_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&lp_GRH_New_Variety_sectionMap___redArg___closed__0, &lp_GRH_New_Variety_sectionMap___redArg___closed__0_once, _init_lp_GRH_New_Variety_sectionMap___redArg___closed__0);
v_toFun_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_toFun_90_);
v___x_91_ = lean_apply_1(v_toFun_90_, v_q_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap(lean_object* v_C_92_, lean_object* v_inst_93_, lean_object* v_X_94_, lean_object* v_q_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lp_GRH_New_Variety_sectionMap___redArg(v_q_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_sectionMap___boxed(lean_object* v_C_97_, lean_object* v_inst_98_, lean_object* v_X_99_, lean_object* v_q_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lp_GRH_New_Variety_sectionMap(v_C_97_, v_inst_98_, v_X_99_, v_q_100_);
lean_dec_ref(v_X_99_);
lean_dec_ref(v_inst_98_);
return v_res_101_;
}
}
static lean_object* _init_lp_GRH_New_Variety_elementsProj___redArg___closed__0(void){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lp_mathlib_CategoryTheory_Functor_Elements_00_u03c0___redArg();
return v___x_102_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___redArg(){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&lp_GRH_New_Variety_elementsProj___redArg___closed__0, &lp_GRH_New_Variety_elementsProj___redArg___closed__0_once, _init_lp_GRH_New_Variety_elementsProj___redArg___closed__0);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___redArg___boxed(lean_object* v___dummy_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_GRH_New_Variety_elementsProj___redArg();
return v_res_106_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj(lean_object* v_C_107_, lean_object* v_inst_108_, lean_object* v_X_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&lp_GRH_New_Variety_elementsProj___redArg___closed__0, &lp_GRH_New_Variety_elementsProj___redArg___closed__0_once, _init_lp_GRH_New_Variety_elementsProj___redArg___closed__0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_elementsProj___boxed(lean_object* v_C_111_, lean_object* v_inst_112_, lean_object* v_X_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = lp_GRH_New_Variety_elementsProj(v_C_111_, v_inst_112_, v_X_113_);
lean_dec_ref(v_X_113_);
lean_dec_ref(v_inst_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___lam__0(lean_object* v_a_115_){
_start:
{
lean_object* v_val_116_; 
v_val_116_ = lean_ctor_get(v_a_115_, 1);
lean_inc(v_val_116_);
return v_val_116_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___lam__0___boxed(lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_GRH_New_Variety_tautologicalSection___redArg___lam__0(v_a_117_);
lean_dec_ref(v_a_117_);
return v_res_118_;
}
}
static lean_object* _init_lp_GRH_New_Variety_tautologicalSection___redArg___closed__1(void){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
v___f_120_ = ((lean_object*)(lp_GRH_New_Variety_tautologicalSection___redArg___closed__0));
v___x_121_ = lp_GRH_New_Variety_sectionMap___redArg(v___f_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg(){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_GRH_New_Variety_tautologicalSection___redArg___closed__1, &lp_GRH_New_Variety_tautologicalSection___redArg___closed__1_once, _init_lp_GRH_New_Variety_tautologicalSection___redArg___closed__1);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___redArg___boxed(lean_object* v___dummy_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_GRH_New_Variety_tautologicalSection___redArg();
return v_res_125_;
}
}
static lean_object* _init_lp_GRH_New_Variety_tautologicalSection___closed__0(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_GRH_New_Variety_tautologicalSection___redArg();
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection(lean_object* v_C_127_, lean_object* v_inst_128_, lean_object* v_X_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&lp_GRH_New_Variety_tautologicalSection___closed__0, &lp_GRH_New_Variety_tautologicalSection___closed__0_once, _init_lp_GRH_New_Variety_tautologicalSection___closed__0);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_tautologicalSection___boxed(lean_object* v_C_131_, lean_object* v_inst_132_, lean_object* v_X_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_GRH_New_Variety_tautologicalSection(v_C_131_, v_inst_132_, v_X_133_);
lean_dec_ref(v_X_133_);
lean_dec_ref(v_inst_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0(lean_object* v_A_135_){
_start:
{
lean_object* v_commRing_136_; 
v_commRing_136_ = lean_ctor_get(v_A_135_, 0);
lean_inc_ref(v_commRing_136_);
return v_commRing_136_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0___boxed(lean_object* v_A_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = lp_GRH_New_Variety_TestOver_toTest___redArg___lam__0(v_A_137_);
lean_dec_ref(v_A_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1(lean_object* v_X_139_, lean_object* v_Y_140_, lean_object* v_f_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_1(v_f_141_, v___y_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1___boxed(lean_object* v_X_144_, lean_object* v_Y_145_, lean_object* v_f_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_GRH_New_Variety_TestOver_toTest___redArg___lam__1(v_X_144_, v_Y_145_, v_f_146_, v___y_147_);
lean_dec_ref(v_Y_145_);
lean_dec_ref(v_X_144_);
return v_res_148_;
}
}
static lean_object* _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2(void){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lp_mathlib_CategoryTheory_ObjectProperty_00_u03b9___redArg();
return v___x_151_;
}
}
static lean_object* _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = ((lean_object*)(lp_GRH_New_Variety_TestOver_toTest___redArg___closed__3));
v___x_156_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2, &lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2_once, _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2);
v___x_157_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4, &lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4_once, _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__4);
v___x_159_ = lp_mathlib_CategoryTheory_ObjectProperty_lift___redArg(v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg(){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5, &lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5_once, _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__5);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___redArg___boxed(lean_object* v___dummy_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_GRH_New_Variety_TestOver_toTest___redArg();
return v_res_163_;
}
}
static lean_object* _init_lp_GRH_New_Variety_TestOver_toTest___closed__0(void){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lp_GRH_New_Variety_TestOver_toTest___redArg();
return v___x_164_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest(lean_object* v_A_165_, lean_object* v_inst_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TestOver_toTest___boxed(lean_object* v_A_168_, lean_object* v_inst_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = lp_GRH_New_Variety_TestOver_toTest(v_A_168_, v_inst_169_);
lean_dec_ref(v_inst_169_);
return v_res_170_;
}
}
static lean_object* _init_lp_GRH_New_Variety_ringOf___redArg___closed__0(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2, &lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2_once, _init_lp_GRH_New_Variety_TestOver_toTest___redArg___closed__2);
v___x_172_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_173_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_172_, v___x_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf___redArg(lean_object* v_g_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&lp_GRH_New_Variety_ringOf___redArg___closed__0, &lp_GRH_New_Variety_ringOf___redArg___closed__0_once, _init_lp_GRH_New_Variety_ringOf___redArg___closed__0);
v___x_176_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_174_, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf(lean_object* v_C_177_, lean_object* v_inst_178_, lean_object* v_A_179_, lean_object* v_inst_180_, lean_object* v_g_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_obj_once(&lp_GRH_New_Variety_ringOf___redArg___closed__0, &lp_GRH_New_Variety_ringOf___redArg___closed__0_once, _init_lp_GRH_New_Variety_ringOf___redArg___closed__0);
v___x_183_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_ringOf___boxed(lean_object* v_C_184_, lean_object* v_inst_185_, lean_object* v_A_186_, lean_object* v_inst_187_, lean_object* v_g_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = lp_GRH_New_Variety_ringOf(v_C_184_, v_inst_185_, v_A_186_, v_inst_187_, v_g_188_);
lean_dec_ref(v_inst_187_);
lean_dec_ref(v_inst_185_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong___redArg(lean_object* v_00_u2113_190_, lean_object* v_g_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_toRing_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_192_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_190_);
v___x_193_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_192_);
v_toRing_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc_ref(v_toRing_194_);
lean_dec_ref(v___x_193_);
v___x_195_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_196_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_194_);
v___x_197_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = lp_GRH_New_Variety_locConstCoeff(v___x_197_);
v___x_199_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_195_, v___x_198_);
v___x_200_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_191_, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong(lean_object* v_C_201_, lean_object* v_inst_202_, lean_object* v_A_203_, lean_object* v_inst_204_, lean_object* v_00_u2113_205_, lean_object* v_g_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_toRing_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_208_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_205_);
v___x_209_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_208_);
v_toRing_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_toRing_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_212_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_210_);
v___x_213_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_212_);
lean_dec_ref(v___x_212_);
v___x_214_ = lp_GRH_New_Variety_locConstCoeff(v___x_213_);
v___x_215_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_211_, v___x_214_);
v___x_216_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_206_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_locConstAlong___boxed(lean_object* v_C_217_, lean_object* v_inst_218_, lean_object* v_A_219_, lean_object* v_inst_220_, lean_object* v_00_u2113_221_, lean_object* v_g_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = lp_GRH_New_Variety_locConstAlong(v_C_217_, v_inst_218_, v_A_219_, v_inst_220_, v_00_u2113_221_, v_g_222_, v_inst_223_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_218_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___redArg(){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___redArg___boxed(lean_object* v___dummy_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_GRH_New_Variety_killingMaps___redArg();
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps(lean_object* v_C_229_, lean_object* v_inst_230_, lean_object* v_00_u03b9_231_, lean_object* v_c_232_, lean_object* v_I_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_killingMaps___boxed(lean_object* v_C_235_, lean_object* v_inst_236_, lean_object* v_00_u03b9_237_, lean_object* v_c_238_, lean_object* v_I_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = lp_GRH_New_Variety_killingMaps(v_C_235_, v_inst_236_, v_00_u03b9_237_, v_c_238_, v_I_239_);
lean_dec(v_c_238_);
lean_dec_ref(v_00_u03b9_237_);
lean_dec_ref(v_inst_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___redArg___lam__0(lean_object* v_00_u03c6_241_, lean_object* v_I_242_, lean_object* v_c_243_){
_start:
{
lean_object* v_obj_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_obj_244_ = lean_ctor_get(v_00_u03c6_241_, 0);
lean_inc(v_obj_244_);
lean_dec_ref(v_00_u03c6_241_);
v___x_245_ = lean_apply_1(v_obj_244_, v_c_243_);
v___x_246_ = lean_apply_1(v_I_242_, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___redArg(lean_object* v_I_247_, lean_object* v_00_u03c6_248_){
_start:
{
lean_object* v___f_249_; 
v___f_249_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_IdealFamily_whisker___redArg___lam__0), 3, 2);
lean_closure_set(v___f_249_, 0, v_00_u03c6_248_);
lean_closure_set(v___f_249_, 1, v_I_247_);
return v___f_249_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker(lean_object* v_C_250_, lean_object* v_C_x27_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_00_u03b9_254_, lean_object* v_I_255_, lean_object* v_00_u03c6_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_IdealFamily_whisker___redArg___lam__0), 3, 2);
lean_closure_set(v___f_257_, 0, v_00_u03c6_256_);
lean_closure_set(v___f_257_, 1, v_I_255_);
return v___f_257_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_whisker___boxed(lean_object* v_C_258_, lean_object* v_C_x27_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_00_u03b9_262_, lean_object* v_I_263_, lean_object* v_00_u03c6_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = lp_GRH_New_Variety_IdealFamily_whisker(v_C_258_, v_C_x27_259_, v_inst_260_, v_inst_261_, v_00_u03b9_262_, v_I_263_, v_00_u03c6_264_);
lean_dec_ref(v_00_u03b9_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___redArg(){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___redArg___boxed(lean_object* v___dummy_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_GRH_New_Variety_IdealFamily_botLocus___redArg();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus(lean_object* v_C_270_, lean_object* v_inst_271_, lean_object* v_00_u03b9_272_, lean_object* v_I_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_box(0);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_botLocus___boxed(lean_object* v_C_275_, lean_object* v_inst_276_, lean_object* v_00_u03b9_277_, lean_object* v_I_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = lp_GRH_New_Variety_IdealFamily_botLocus(v_C_275_, v_inst_276_, v_00_u03b9_277_, v_I_278_);
lean_dec_ref(v_I_278_);
lean_dec_ref(v_00_u03b9_277_);
lean_dec_ref(v_inst_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___redArg(){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_box(0);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___redArg___boxed(lean_object* v___dummy_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lp_GRH_New_Variety_IdealFamily_topLocus___redArg();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus(lean_object* v_C_284_, lean_object* v_inst_285_, lean_object* v_00_u03b9_286_, lean_object* v_I_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_topLocus___boxed(lean_object* v_C_289_, lean_object* v_inst_290_, lean_object* v_00_u03b9_291_, lean_object* v_I_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = lp_GRH_New_Variety_IdealFamily_topLocus(v_C_289_, v_inst_290_, v_00_u03b9_291_, v_I_292_);
lean_dec_ref(v_I_292_);
lean_dec_ref(v_00_u03b9_291_);
lean_dec_ref(v_inst_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__0(lean_object* v_G_294_, lean_object* v_c_295_){
_start:
{
lean_object* v_obj_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_obj_296_ = lean_ctor_get(v_G_294_, 0);
lean_inc(v_obj_296_);
lean_dec_ref(v_G_294_);
v___x_297_ = lean_apply_1(v_obj_296_, v_c_295_);
v___x_298_ = lean_box(0);
v___x_299_ = lp_mathlib_QuotientAddGroup_Quotient_addGroup___redArg(v___x_297_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__1(lean_object* v_G_300_, lean_object* v_X_301_, lean_object* v_Y_302_, lean_object* v_f_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_obj_305_; lean_object* v_map_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_54__overap_310_; lean_object* v___x_311_; 
v_obj_305_ = lean_ctor_get(v_G_300_, 0);
lean_inc(v_obj_305_);
v_map_306_ = lean_ctor_get(v_G_300_, 1);
lean_inc(v_map_306_);
lean_dec_ref(v_G_300_);
lean_inc(v_Y_302_);
v___x_307_ = lean_apply_1(v_obj_305_, v_Y_302_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_apply_3(v_map_306_, v_X_301_, v_Y_302_, v_f_303_);
v___x_54__overap_310_ = lp_mathlib_QuotientAddGroup_map___redArg(v___x_307_, v___x_308_, v___x_309_);
v___x_311_ = lean_apply_1(v___x_54__overap_310_, v___y_304_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(lean_object* v_G_312_){
_start:
{
lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
lean_inc_ref(v_G_312_);
v___f_313_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__0), 2, 1);
lean_closure_set(v___f_313_, 0, v_G_312_);
v___f_314_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg___lam__1), 5, 1);
lean_closure_set(v___f_314_, 0, v_G_312_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___f_313_);
lean_ctor_set(v___x_315_, 1, v___f_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff(lean_object* v_C_316_, lean_object* v_inst_317_, lean_object* v_G_318_, lean_object* v_00_u03b9_319_, lean_object* v_I_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(v_G_318_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_zerosCoeff___boxed(lean_object* v_C_322_, lean_object* v_inst_323_, lean_object* v_G_324_, lean_object* v_00_u03b9_325_, lean_object* v_I_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = lp_GRH_New_Variety_IdealFamily_zerosCoeff(v_C_322_, v_inst_323_, v_G_324_, v_00_u03b9_325_, v_I_326_);
lean_dec_ref(v_I_326_);
lean_dec_ref(v_00_u03b9_325_);
lean_dec_ref(v_inst_323_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0(lean_object* v_x_328_, lean_object* v___y_329_){
_start:
{
lean_inc(v___y_329_);
return v___y_329_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0___boxed(lean_object* v_x_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___lam__0(v_x_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec(v_x_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg(){
_start:
{
lean_object* v___f_335_; 
v___f_335_ = ((lean_object*)(lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0));
return v___f_335_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___boxed(lean_object* v___dummy_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg();
return v_res_337_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff(lean_object* v_C_338_, lean_object* v_inst_339_, lean_object* v_G_340_, lean_object* v_00_u03b9_341_, lean_object* v_I_342_){
_start:
{
lean_object* v___f_343_; 
v___f_343_ = ((lean_object*)(lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0));
return v___f_343_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_toZerosCoeff___boxed(lean_object* v_C_344_, lean_object* v_inst_345_, lean_object* v_G_346_, lean_object* v_00_u03b9_347_, lean_object* v_I_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = lp_GRH_New_Variety_IdealFamily_toZerosCoeff(v_C_344_, v_inst_345_, v_G_346_, v_00_u03b9_347_, v_I_348_);
lean_dec_ref(v_I_348_);
lean_dec_ref(v_00_u03b9_347_);
lean_dec_ref(v_G_346_);
lean_dec_ref(v_inst_345_);
return v_res_349_;
}
}
static lean_object* _init_lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0(void){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = lp_mathlib_CategoryTheory_Functor_id___redArg();
return v___x_350_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant___redArg(lean_object* v_00_u2113_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_toRing_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_352_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_351_);
v___x_353_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_352_);
v_toRing_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc_ref(v_toRing_354_);
lean_dec_ref(v___x_353_);
v___x_355_ = lean_obj_once(&lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0, &lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0_once, _init_lp_GRH_New_Variety_Theory_locallyConstant___redArg___closed__0);
v___x_356_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_357_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_354_);
v___x_358_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_357_);
lean_dec_ref(v___x_357_);
v___x_359_ = lp_GRH_New_Variety_locConstCoeff(v___x_358_);
v___x_360_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_356_, v___x_359_);
v___x_361_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_355_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant(lean_object* v_A_362_, lean_object* v_inst_363_, lean_object* v_00_u2113_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lp_GRH_New_Variety_Theory_locallyConstant___redArg(v_00_u2113_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_locallyConstant___boxed(lean_object* v_A_367_, lean_object* v_inst_368_, lean_object* v_00_u2113_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = lp_GRH_New_Variety_Theory_locallyConstant(v_A_367_, v_inst_368_, v_00_u2113_369_, v_inst_370_);
lean_dec_ref(v_inst_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg___lam__0(lean_object* v_00_u2113_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_toRing_378_; lean_object* v___x_379_; lean_object* v_toAddMonoidWithOne_380_; lean_object* v_toOne_381_; 
v___x_376_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_372_);
v___x_377_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_376_);
v_toRing_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc_ref(v_toRing_378_);
lean_dec_ref(v___x_377_);
v___x_379_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_378_);
v_toAddMonoidWithOne_380_ = lean_ctor_get(v___x_379_, 1);
lean_inc_ref(v_toAddMonoidWithOne_380_);
lean_dec_ref(v___x_379_);
v_toOne_381_ = lean_ctor_get(v_toAddMonoidWithOne_380_, 2);
lean_inc(v_toOne_381_);
lean_dec_ref(v_toAddMonoidWithOne_380_);
return v_toOne_381_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg___lam__0___boxed(lean_object* v_00_u2113_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = lp_GRH_New_Variety_oneLocConst___redArg___lam__0(v_00_u2113_382_, v_x_383_, v_x_384_, v___y_385_);
lean_dec(v_x_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___redArg(lean_object* v_00_u2113_387_, lean_object* v_g_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_toRing_391_; lean_object* v___f_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___f_399_; 
lean_inc(v_00_u2113_387_);
v___x_389_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_387_);
v___x_390_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_389_);
v_toRing_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_toRing_391_);
lean_dec_ref(v___x_390_);
v___f_392_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_oneLocConst___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_392_, 0, v_00_u2113_387_);
v___x_393_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_394_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_391_);
v___x_395_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = lp_GRH_New_Variety_locConstCoeff(v___x_395_);
v___x_397_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_393_, v___x_396_);
v___x_398_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_388_, v___x_397_);
v___f_399_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_freeAb_desc___redArg___lam__0), 4, 2);
lean_closure_set(v___f_399_, 0, v___x_398_);
lean_closure_set(v___f_399_, 1, v___f_392_);
return v___f_399_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst(lean_object* v_C_400_, lean_object* v_inst_401_, lean_object* v_A_402_, lean_object* v_inst_403_, lean_object* v_00_u2113_404_, lean_object* v_inst_405_, lean_object* v_g_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lp_GRH_New_Variety_oneLocConst___redArg(v_00_u2113_404_, v_g_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_oneLocConst___boxed(lean_object* v_C_408_, lean_object* v_inst_409_, lean_object* v_A_410_, lean_object* v_inst_411_, lean_object* v_00_u2113_412_, lean_object* v_inst_413_, lean_object* v_g_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = lp_GRH_New_Variety_oneLocConst(v_C_408_, v_inst_409_, v_A_410_, v_inst_411_, v_00_u2113_412_, v_inst_413_, v_g_414_);
lean_dec_ref(v_inst_411_);
lean_dec_ref(v_inst_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements___redArg(lean_object* v_M_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&lp_GRH_New_Variety_elementsProj___redArg___closed__0, &lp_GRH_New_Variety_elementsProj___redArg___closed__0_once, _init_lp_GRH_New_Variety_elementsProj___redArg___closed__0);
v___x_418_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_417_, v_M_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements(lean_object* v_C_419_, lean_object* v_inst_420_, lean_object* v_X_421_, lean_object* v_A_422_, lean_object* v_inst_423_, lean_object* v_00_u2113_424_, lean_object* v_inst_425_, lean_object* v_g_426_, lean_object* v_M_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lp_GRH_New_Variety_TorsionCoeff_onElements___redArg(v_M_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_TorsionCoeff_onElements___boxed(lean_object* v_C_429_, lean_object* v_inst_430_, lean_object* v_X_431_, lean_object* v_A_432_, lean_object* v_inst_433_, lean_object* v_00_u2113_434_, lean_object* v_inst_435_, lean_object* v_g_436_, lean_object* v_M_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = lp_GRH_New_Variety_TorsionCoeff_onElements(v_C_429_, v_inst_430_, v_X_431_, v_A_432_, v_inst_433_, v_00_u2113_434_, v_inst_435_, v_g_436_, v_M_437_);
lean_dec_ref(v_g_436_);
lean_dec(v_00_u2113_434_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_X_431_);
lean_dec_ref(v_inst_430_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements___redArg(lean_object* v_00_u0398_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lp_GRH_New_Variety_TorsionCoeff_onElements___redArg(v_00_u0398_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements(lean_object* v_C_441_, lean_object* v_inst_442_, lean_object* v_X_443_, lean_object* v_A_444_, lean_object* v_inst_445_, lean_object* v_00_u2113_446_, lean_object* v_inst_447_, lean_object* v_g_448_, lean_object* v_00_u0398_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = lp_GRH_New_Variety_TorsionCoeff_onElements___redArg(v_00_u0398_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onElements___boxed(lean_object* v_C_451_, lean_object* v_inst_452_, lean_object* v_X_453_, lean_object* v_A_454_, lean_object* v_inst_455_, lean_object* v_00_u2113_456_, lean_object* v_inst_457_, lean_object* v_g_458_, lean_object* v_00_u0398_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = lp_GRH_New_Variety_Theory_onElements(v_C_451_, v_inst_452_, v_X_453_, v_A_454_, v_inst_455_, v_00_u2113_456_, v_inst_457_, v_g_458_, v_00_u0398_459_);
lean_dec_ref(v_g_458_);
lean_dec(v_00_u2113_456_);
lean_dec_ref(v_inst_455_);
lean_dec_ref(v_X_453_);
lean_dec_ref(v_inst_452_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros___redArg(lean_object* v_00_u0398_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(v_00_u0398_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros(lean_object* v_C_463_, lean_object* v_inst_464_, lean_object* v_A_465_, lean_object* v_inst_466_, lean_object* v_00_u2113_467_, lean_object* v_inst_468_, lean_object* v_g_469_, lean_object* v_00_u0398_470_, lean_object* v_I_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(v_00_u0398_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_Theory_onZeros___boxed(lean_object* v_C_473_, lean_object* v_inst_474_, lean_object* v_A_475_, lean_object* v_inst_476_, lean_object* v_00_u2113_477_, lean_object* v_inst_478_, lean_object* v_g_479_, lean_object* v_00_u0398_480_, lean_object* v_I_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = lp_GRH_New_Variety_Theory_onZeros(v_C_473_, v_inst_474_, v_A_475_, v_inst_476_, v_00_u2113_477_, v_inst_478_, v_g_479_, v_00_u0398_480_, v_I_481_);
lean_dec_ref(v_I_481_);
lean_dec_ref(v_g_479_);
lean_dec(v_00_u2113_477_);
lean_dec_ref(v_inst_476_);
lean_dec_ref(v_inst_474_);
return v_res_482_;
}
}
static lean_object* _init_lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lp_GRH_New_Variety_freeAb___redArg();
return v___x_483_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros___redArg(lean_object* v_00_u2113_484_, lean_object* v_g_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_toRing_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_obj_493_; lean_object* v___x_494_; lean_object* v_obj_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___f_507_; 
v___x_486_ = lp_mathlib_AddCommGrpCat_instCategory;
lean_inc(v_00_u2113_484_);
v___x_487_ = lp_mathlib_ZMod_instField___redArg(v_00_u2113_484_);
v___x_488_ = lp_mathlib_Field_toDivisionRing___redArg(v___x_487_);
v_toRing_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc_ref(v_toRing_489_);
lean_dec_ref(v___x_488_);
v___x_490_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_489_);
v___x_491_ = lp_mathlib_AddGroupWithOne_toAddGroup___redArg(v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = lean_obj_once(&lp_GRH_New_Variety_onePointFunctor___redArg___closed__0, &lp_GRH_New_Variety_onePointFunctor___redArg___closed__0_once, _init_lp_GRH_New_Variety_onePointFunctor___redArg___closed__0);
v_obj_493_ = lean_ctor_get(v___x_492_, 0);
v___x_494_ = lean_obj_once(&lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0, &lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0_once, _init_lp_GRH_New_Variety_IdealFamily_constToZeros___redArg___closed__0);
v_obj_495_ = lean_ctor_get(v___x_494_, 0);
v___x_496_ = lean_obj_once(&lp_GRH_New_Variety_TestOver_toTest___closed__0, &lp_GRH_New_Variety_TestOver_toTest___closed__0_once, _init_lp_GRH_New_Variety_TestOver_toTest___closed__0);
v___x_497_ = lp_GRH_New_Variety_locConstCoeff(v___x_491_);
v___x_498_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v___x_496_, v___x_497_);
lean_inc_ref(v_g_485_);
v___x_499_ = lp_mathlib_CategoryTheory_Functor_comp___redArg(v_g_485_, v___x_498_);
lean_inc_ref(v___x_499_);
v___x_500_ = lp_GRH_New_Variety_IdealFamily_zerosCoeff___redArg(v___x_499_);
lean_inc(v_obj_493_);
v___x_501_ = lean_apply_1(v_obj_493_, lean_box(0));
lean_inc(v_obj_495_);
v___x_502_ = lean_apply_1(v_obj_495_, v___x_501_);
v___x_503_ = lp_GRH_New_Variety_oneLocConst___redArg(v_00_u2113_484_, v_g_485_);
v___f_504_ = ((lean_object*)(lp_GRH_New_Variety_IdealFamily_toZerosCoeff___redArg___closed__0));
v___f_505_ = lean_alloc_closure((void*)(lp_mathlib_CategoryTheory_NatTrans_vcomp___redArg___lam__0), 7, 6);
lean_closure_set(v___f_505_, 0, v___x_486_);
lean_closure_set(v___f_505_, 1, v___x_502_);
lean_closure_set(v___f_505_, 2, v___x_499_);
lean_closure_set(v___f_505_, 3, v___x_500_);
lean_closure_set(v___f_505_, 4, v___x_503_);
lean_closure_set(v___f_505_, 5, v___f_504_);
v___f_506_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abCoker_desc___redArg___lam__0), 3, 1);
lean_closure_set(v___f_506_, 0, v___f_505_);
v___f_507_ = lean_alloc_closure((void*)(lp_GRH_New_Variety_abCoker_desc___redArg___lam__0), 3, 1);
lean_closure_set(v___f_507_, 0, v___f_506_);
return v___f_507_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros(lean_object* v_C_508_, lean_object* v_inst_509_, lean_object* v_A_510_, lean_object* v_inst_511_, lean_object* v_00_u2113_512_, lean_object* v_inst_513_, lean_object* v_g_514_, lean_object* v_I_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lp_GRH_New_Variety_IdealFamily_constToZeros___redArg(v_00_u2113_512_, v_g_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Variety_IdealFamily_constToZeros___boxed(lean_object* v_C_517_, lean_object* v_inst_518_, lean_object* v_A_519_, lean_object* v_inst_520_, lean_object* v_00_u2113_521_, lean_object* v_inst_522_, lean_object* v_g_523_, lean_object* v_I_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = lp_GRH_New_Variety_IdealFamily_constToZeros(v_C_517_, v_inst_518_, v_A_519_, v_inst_520_, v_00_u2113_521_, v_inst_522_, v_g_523_, v_I_524_);
lean_dec_ref(v_I_524_);
lean_dec_ref(v_inst_520_);
lean_dec_ref(v_inst_518_);
return v_res_525_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_Lib_Adelic_Unitary_Defs(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_Etale_RelativeChains(uint8_t builtin);
lean_object* initialize_GRH_Lib_Cohomology_LerayHirsch(uint8_t builtin);
lean_object* initialize_GRH_Lib_General_Algebra_CohomologyBaseChange(uint8_t builtin);
lean_object* initialize_GRH_Lib_PadicComparison_HodgeTate_ExtCocycles(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_Lib_Cohomology_TorsionTheories(uint8_t builtin) {
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
res = initialize_GRH_Lib_Adelic_Unitary_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_Etale_RelativeChains(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_Cohomology_LerayHirsch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_General_Algebra_CohomologyBaseChange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GRH_Lib_PadicComparison_HodgeTate_ExtCocycles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
