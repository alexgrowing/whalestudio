import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsPic

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain WithZero

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

noncomputable def mulPullback (n : ℤ) (hn : n ≠ 0) :
    W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField :=
  (mulIsogeny W n hn).comap

omit [DecidableEq F] in
theorem mulPullback_genX {n : ℤ} (hn : n ≠ 0) :
    mulPullback W n hn (genX W) = aeval (genX W) (W.Φ n) / aeval (genX W) (W.ΨSq n) := by
  rw [mulPullback, Isogeny.comap_genX, mulIsogeny_alt]

omit [DecidableEq F] in
theorem map_mulPullback_genericPoint {n : ℤ} (hn : n ≠ 0) :
    Point.map (mulPullback W n hn) (genericPoint W) = n • genericPoint W := by
  obtain ⟨h, he⟩ := eq_some_xOf_yOf _ (zsmul_genericPoint_ne_zero W hn)
  rw [mulPullback, Isogeny.comap, map_liftPoint_genericPoint]
  exact he.symm

variable [IsAlgClosed F]

theorem translate_comp_mulPullback {n : ℤ} (hn : n ≠ 0) (P : W.toAffine.Point) :
    (translate W P).comp (mulPullback W n hn) = (mulPullback W n hn).comp (translate W (n • P)) := by
  apply algHom_eq_of_map_genericPoint
  rw [← Point.map_map, ← Point.map_map, map_mulPullback_genericPoint, map_zsmul,
    map_translate_genericPoint, map_translate_genericPoint, map_add, map_mulPullback_genericPoint,
    map_constPoint, zsmul_add, map_zsmul]

omit [DecidableEq F] [W.IsElliptic] [IsAlgClosed F] in

theorem aeval_genX (p : F[X]) :
    aeval (genX W) p = algebraMap F[X] W.toAffine.FunctionField p := by
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem valuationInfty_algebraMap_const_eq_one {c : F} (hc : c ≠ 0) :
    valuationInfty W (algebraMap F W.toAffine.FunctionField c) = 1 := by
  rw [valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
    ordInfty_algebraMap_const W hc, neg_zero, exp_zero]

omit [IsAlgClosed F] [DecidableEq F] in

theorem valuationInfty_mulPullback {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    (f : W.toAffine.FunctionField) :
    valuationInfty W (mulPullback W n hn0 f) = valuationInfty W f := by
  let w := (valuationInfty W).comap (mulPullback W n hn0).toRingHom
  have hwapp : ∀ g, w g = valuationInfty W (mulPullback W n hn0 g) := fun g => rfl
  have hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1 := fun c hc => by
    rw [hwapp, AlgHom.commutes, valuationInfty_algebraMap_const_eq_one W hc]
  have hΦ0 : W.Φ n ≠ 0 := by
    intro h
    have := W.natDegree_Φ n
    rw [h, natDegree_zero] at this
    have : 0 < n.natAbs ^ 2 := by positivity
    omega
  have hΨ0 : W.ΨSq n ≠ 0 := ΨSq_ne_zero_of_ne_zero W hn0
  have hvF : ∀ c : F, c ≠ 0 → valuationInfty W (algebraMap F W.toAffine.FunctionField c) = 1 :=
    fun c hc => valuationInfty_algebraMap_const_eq_one W hc
  have hΦ := valuation_poly_of_one_lt (valuationInfty W) hvF two_pos (valuationInfty_genX W) hΦ0
  have hΨ := valuation_poly_of_one_lt (valuationInfty W) hvF two_pos (valuationInfty_genX W) hΨ0
  rw [W.natDegree_Φ n] at hΦ
  rw [W.natDegree_ΨSq hn] at hΨ
  have hx : w (genX W) = exp 2 := by
    rw [hwapp, mulPullback_genX, aeval_genX, aeval_genX, map_div₀, hΦ, hΨ, ← exp_sub]
    congr 1
    have h1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn0)
    push_cast [Nat.cast_sub h1]
    ring
  exact DFunLike.congr_fun (eq_valuationInfty_of_genX w hF hx) f

theorem valuationPoint_mulPullback {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    (P : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    valuationPoint W P (mulPullback W n hn0 f) = valuationPoint W (n • P) f := by
  rw [← valuationInfty_translate, ← valuationInfty_translate,
    ← valuationInfty_mulPullback W hn hn0 (translate W (n • P) f)]
  exact congrArg (valuationInfty W) (DFunLike.congr_fun (translate_comp_mulPullback W hn0 P) f)

theorem ordPoint_mulPullback {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0) (P : W.toAffine.Point)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    ordPoint W P (mulPullback W n hn0 f) = ordPoint W (n • P) f := by
  have hf' : mulPullback W n hn0 f ≠ 0 := (map_ne_zero_iff _ (mulPullback W n hn0).injective).mpr hf
  have h := valuationPoint_mulPullback W hn hn0 P f
  rw [valuationPoint_eq_exp W P hf', valuationPoint_eq_exp W (n • P) hf, exp_inj] at h
  exact neg_injective h

theorem finite_setOf_zsmul_eq {n : ℤ} (hn : (n : F) ≠ 0) (Q : W.toAffine.Point) :
    {P : W.toAffine.Point | n • P = Q}.Finite := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hcard := card_zsmul_eq_zero W hn
  have hker : {P : W.toAffine.Point | n • P = 0}.Finite := by
    rw [← Set.finite_coe_iff]
    refine Nat.finite_of_card_ne_zero ?_
    change Nat.card {P : W.toAffine.Point // n • P = 0} ≠ 0
    rw [hcard]
    positivity
  rcases Set.eq_empty_or_nonempty {P : W.toAffine.Point | n • P = Q} with h | ⟨P₀, hP₀⟩
  · rw [h]; exact Set.finite_empty
  · refine (hker.image (· + P₀)).subset fun P hP => ⟨P - P₀, ?_, sub_add_cancel P P₀⟩
    change n • (P - P₀) = 0
    rw [zsmul_sub, hP, hP₀.out, sub_self]

noncomputable def mulPullbackDivisor {n : ℤ} (hn : (n : F) ≠ 0) :
    CurveDivisor W →+ CurveDivisor W where
  toFun D := Finsupp.ofSupportFinite (fun P => D (n • P)) (by
    refine (D.support.finite_toSet.biUnion fun Q _ => finite_setOf_zsmul_eq W hn Q).subset ?_
    intro P hP
    exact Set.mem_biUnion (Finsupp.mem_support_iff.mpr hP) rfl)
  map_zero' := by ext P; rfl
  map_add' D D' := by ext P; rfl

theorem mulPullbackDivisor_apply {n : ℤ} (hn : (n : F) ≠ 0) (D : CurveDivisor W)
    (P : W.toAffine.Point) : mulPullbackDivisor W hn D P = D (n • P) := rfl

theorem divisorOf_mulPullback {n : ℤ} (hn : (n : F) ≠ 0) (hn0 : n ≠ 0)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    divisorOf W (mulPullback W n hn0 f) = mulPullbackDivisor W hn (divisorOf W f) := by
  ext P
  rw [divisorOf_apply, mulPullbackDivisor_apply, divisorOf_apply, ordPoint_mulPullback W hn hn0 P hf]

end GroundTheory.Arith.Abelian
