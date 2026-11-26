// Lean compiler output
// Module: New.Congruences.Lifting.SidePoints
// Imports: public import Init public meta import Init public import New.Congruences.Lifting.CupProductBound
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
lean_object* lp_GRH_New_Lift_KummerChart_stdOrders(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_mathlib_LinearMap_inl___redArg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_raisedOrdersAtZero___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_raisedOrdersAtZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_raisedOrdersAtZero___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_plainDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_plainDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_stopOrders(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_stopOrders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0;
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_raisedOrdersAtZero(lean_object* v_t_3_, lean_object* v_a_4_, lean_object* v_u_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_dec_eq(v_a_4_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___x_9_ = lean_int_sub(v___x_8_, v_u_5_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_int_sub(v_t_3_, v_u_5_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_raisedOrdersAtZero___boxed(lean_object* v_t_11_, lean_object* v_a_12_, lean_object* v_u_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_GRH_New_Lift_raisedOrdersAtZero(v_t_11_, v_a_12_, v_u_13_);
lean_dec(v_u_13_);
lean_dec(v_a_12_);
lean_dec(v_t_11_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___redArg(lean_object* v_S_15_){
_start:
{
lean_object* v_paramLattice_16_; lean_object* v_addCommGroup_17_; lean_object* v_toAddMonoid_18_; lean_object* v___x_19_; 
v_paramLattice_16_ = lean_ctor_get(v_S_15_, 1);
v_addCommGroup_17_ = lean_ctor_get(v_paramLattice_16_, 0);
v_toAddMonoid_18_ = lean_ctor_get(v_addCommGroup_17_, 0);
v___x_19_ = lp_mathlib_LinearMap_inl___redArg(v_toAddMonoid_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___redArg___boxed(lean_object* v_S_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___redArg(v_S_20_);
lean_dec_ref(v_S_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer(lean_object* v_p_22_, lean_object* v_inst_23_, lean_object* v_00_u0393_24_, lean_object* v_k_25_, lean_object* v_O_26_, lean_object* v_S_27_){
_start:
{
lean_object* v_paramLattice_28_; lean_object* v_addCommGroup_29_; lean_object* v_toAddMonoid_30_; lean_object* v___x_31_; 
v_paramLattice_28_ = lean_ctor_get(v_S_27_, 1);
v_addCommGroup_29_ = lean_ctor_get(v_paramLattice_28_, 0);
v_toAddMonoid_30_ = lean_ctor_get(v_addCommGroup_29_, 0);
v___x_31_ = lp_mathlib_LinearMap_inl___redArg(v_toAddMonoid_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_inclKer___boxed(lean_object* v_p_32_, lean_object* v_inst_33_, lean_object* v_00_u0393_34_, lean_object* v_k_35_, lean_object* v_O_36_, lean_object* v_S_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = lp_GRH_New_Lift_KummerChart_PairingSide_inclKer(v_p_32_, v_inst_33_, v_00_u0393_34_, v_k_35_, v_O_36_, v_S_37_);
lean_dec_ref(v_S_37_);
lean_dec_ref(v_O_36_);
lean_dec_ref(v_k_35_);
lean_dec_ref(v_00_u0393_34_);
lean_dec(v_p_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(lean_object* v_t_39_, lean_object* v_00_u03b7_40_, lean_object* v_l_41_, lean_object* v_a_42_, lean_object* v_u_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___y_47_; uint8_t v___x_54_; 
v___x_44_ = lean_int_neg(v_u_43_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_nat_dec_eq(v_a_42_, v___x_45_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec(v_t_39_);
v___x_55_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___y_47_ = v___x_55_;
goto v___jp_46_;
}
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_nat_to_int(v_t_39_);
v___y_47_ = v___x_56_;
goto v___jp_46_;
}
v___jp_46_:
{
lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_48_ = lean_int_add(v___x_44_, v___y_47_);
lean_dec(v___y_47_);
lean_dec(v___x_44_);
v___x_49_ = lean_nat_dec_lt(v_a_42_, v_l_41_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_00_u03b7_40_);
v___x_50_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___x_51_ = lean_int_add(v___x_48_, v___x_50_);
lean_dec(v___x_48_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_nat_to_int(v_00_u03b7_40_);
v___x_53_ = lean_int_add(v___x_48_, v___x_52_);
lean_dec(v___x_52_);
lean_dec(v___x_48_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth___boxed(lean_object* v_t_57_, lean_object* v_00_u03b7_58_, lean_object* v_l_59_, lean_object* v_a_60_, lean_object* v_u_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(v_t_57_, v_00_u03b7_58_, v_l_59_, v_a_60_, v_u_61_);
lean_dec(v_u_61_);
lean_dec(v_a_60_);
lean_dec(v_l_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_plainDepth(lean_object* v_t_63_, lean_object* v_00_u03b7_64_, lean_object* v_l_65_, lean_object* v_h_u2080_66_, lean_object* v_a_67_, lean_object* v_u_68_){
_start:
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lp_GRH_New_Lift_KummerChart_PairingSide_standardDepth(v_t_63_, v_00_u03b7_64_, v_l_65_, v_a_67_, v_u_68_);
v___x_70_ = lean_nat_dec_eq(v_a_67_, v_l_65_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_h_u2080_66_);
v___x_71_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___x_72_ = lean_int_add(v___x_69_, v___x_71_);
lean_dec(v___x_69_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_nat_to_int(v_h_u2080_66_);
v___x_74_ = lean_int_add(v___x_69_, v___x_73_);
lean_dec(v___x_73_);
lean_dec(v___x_69_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_plainDepth___boxed(lean_object* v_t_75_, lean_object* v_00_u03b7_76_, lean_object* v_l_77_, lean_object* v_h_u2080_78_, lean_object* v_a_79_, lean_object* v_u_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_GRH_New_Lift_KummerChart_PairingSide_plainDepth(v_t_75_, v_00_u03b7_76_, v_l_77_, v_h_u2080_78_, v_a_79_, v_u_80_);
lean_dec(v_u_80_);
lean_dec(v_a_79_);
lean_dec(v_l_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_stopOrders(lean_object* v_00_u03b7_82_, lean_object* v_l_83_, lean_object* v_a_84_, lean_object* v_u_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___y_89_; uint8_t v___x_92_; 
v___x_86_ = lp_GRH_New_Lift_KummerChart_stdOrders(v_l_83_, v_a_84_, v_u_85_);
v___x_87_ = lean_int_neg(v_u_85_);
v___x_92_ = lean_nat_dec_lt(v_a_84_, v_l_83_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec(v_00_u03b7_82_);
v___x_93_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___y_89_ = v___x_93_;
goto v___jp_88_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = lean_nat_to_int(v_00_u03b7_82_);
v___y_89_ = v___x_94_;
goto v___jp_88_;
}
v___jp_88_:
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = lean_int_sub(v___x_87_, v___y_89_);
lean_dec(v___y_89_);
lean_dec(v___x_87_);
v___x_91_ = lean_int_dec_le(v___x_86_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v___x_90_);
return v___x_86_;
}
else
{
lean_dec(v___x_86_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_stopOrders___boxed(lean_object* v_00_u03b7_95_, lean_object* v_l_96_, lean_object* v_a_97_, lean_object* v_u_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = lp_GRH_New_Lift_KummerChart_PairingSide_stopOrders(v_00_u03b7_95_, v_l_96_, v_a_97_, v_u_98_);
lean_dec(v_u_98_);
lean_dec(v_a_97_);
lean_dec(v_l_96_);
return v_res_99_;
}
}
static lean_object* _init_lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound(lean_object* v_l_102_, lean_object* v_t_103_, lean_object* v_a_104_, lean_object* v_s_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_lt(v_a_104_, v_l_102_);
if (v___x_106_ == 0)
{
uint8_t v___x_107_; 
v___x_107_ = lean_nat_dec_eq(v_a_104_, v_l_102_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_t_103_);
v___x_108_ = lean_obj_once(&lp_GRH_New_Lift_raisedOrdersAtZero___closed__0, &lp_GRH_New_Lift_raisedOrdersAtZero___closed__0_once, _init_lp_GRH_New_Lift_raisedOrdersAtZero___closed__0);
v___x_109_ = lean_int_sub(v___x_108_, v_s_105_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_nat_to_int(v_t_103_);
v___x_111_ = lean_int_sub(v___x_110_, v_s_105_);
lean_dec(v___x_110_);
return v___x_111_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec(v_t_103_);
v___x_112_ = lean_obj_once(&lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0, &lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0_once, _init_lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___closed__0);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound___boxed(lean_object* v_l_113_, lean_object* v_t_114_, lean_object* v_a_115_, lean_object* v_s_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_GRH_New_Lift_KummerChart_PairingSide_ruleBound(v_l_113_, v_t_114_, v_a_115_, v_s_116_);
lean_dec(v_s_116_);
lean_dec(v_a_115_);
lean_dec(v_l_113_);
return v_res_117_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GRH_New_Congruences_Lifting_CupProductBound(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_GRH_New_Congruences_Lifting_SidePoints(uint8_t builtin) {
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
res = initialize_GRH_New_Congruences_Lifting_CupProductBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
