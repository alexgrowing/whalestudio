import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrixStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.SplitWeil

private lemma rpow_half_mul_rpow_inv_eq_one (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * ((t⁻¹) ^ (-a) * s ^ (-b)) = 1 := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_neg]
  have e1 : s ^ (b / 2) * s ^ (b / 2) * s ^ (-b) = 1 := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs, show b / 2 + b / 2 + -b = (0 : ℝ) by ring, Real.rpow_zero]
  have e2 : t ^ (-a / 2) * t ^ (-a / 2) * t ^ a = 1 := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht, show -a / 2 + -a / 2 + a = (0 : ℝ) by ring, Real.rpow_zero]
  calc s ^ (b / 2) * t ^ (-a / 2) * (s ^ (b / 2) * t ^ (-a / 2)) * (t ^ a * s ^ (-b))
      = (s ^ (b / 2) * s ^ (b / 2) * s ^ (-b)) * (t ^ (-a / 2) * t ^ (-a / 2) * t ^ a) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

private lemma isUnit_of_valuation_eq_one' (z : ℂ) (hz : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

private lemma unit_mul_real_mul_conj_eq_real_sq_mul (m1 m2 : ℂ) (h1 : ‖m1‖ = 1) (h2 : ‖m2‖ = 1) (r1 r2 : ℝ) (u v : ℂ) :
    m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * u * (starRingEnd ℂ) (m1 * m2 * (r1 : ℂ) * (r2 : ℂ) * v) =
      ((r1 * r2 * (r1 * r2) : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) := by
  have e1 := isUnit_of_valuation_eq_one' m1 h1
  have e2 := isUnit_of_valuation_eq_one' m2 h2
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination (m2 * (starRingEnd ℂ) m2 * r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e1 +
    (r1 * r2 * r1 * r2 * u * (starRingEnd ℂ) v) * e2

private lemma nabs_pos_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 ((Group.isUnit x).map (distribHaarChar k)).ne_zero)

private lemma nabs_inv_twisted_operators (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : nabs k x⁻¹ = (nabs k x)⁻¹ := by
  show ((distribHaarChar k x⁻¹ : NNReal) : ℝ) = ((distribHaarChar k x : NNReal) : ℝ)⁻¹
  rw [map_inv, NNReal.coe_inv]

theorem ip_om_om : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : ∀ x, ‖(μ x : ℂ)‖ = 1) (g : GL a k) (h : GL b k) (Φ Ψ : Matrix b a k → ℂ), ip ν (om μ g h Φ) (om μ g h Ψ) = ip ν Φ Ψ := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _ μ hμ g h Φ Ψ
  set F : Matrix b a k → ℂ := fun y => Φ y * (starRingEnd ℂ) (Ψ y) with hF
  have hinv : ‖(((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, hμ, inv_one]
  set ng := nabs k (Matrix.GeneralLinearGroup.det g) with hng
  set nh := nabs k (Matrix.GeneralLinearGroup.det h) with hnh
  set c : ℝ := ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2) *
    (ng ^ ((Fintype.card b : ℝ) / 2) * nh ^ (-(Fintype.card a : ℝ) / 2)) with hc
  have hpt : ∀ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) =
      (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) := fun x =>
    unit_mul_real_mul_conj_eq_real_sq_mul _ _ (hμ _) hinv _ _ _ _
  have hT := (GlobalTheory.T.linear_change_of_variables_localField_matrix k a b ν).2 g h⁻¹ F
  have hdet : nabs k (Matrix.GeneralLinearGroup.det h⁻¹) = nh⁻¹ := by
    rw [map_inv, nabs_inv_twisted_operators]
  have hkey : c * (nabs k (Matrix.GeneralLinearGroup.det h⁻¹) ^ (-(Fintype.card a : ℝ)) *
      ng ^ (-(Fintype.card b : ℝ))) = 1 := by
    rw [hdet]
    exact rpow_half_mul_rpow_inv_eq_one ng nh (nabs_pos_twisted_operators k _) (nabs_pos_twisted_operators k _) _ _
  unfold ip
  calc ∫ x, om μ g h Φ x * (starRingEnd ℂ) (om μ g h Ψ x) ∂(volM ν b a)
      = ∫ x, (c : ℂ) * F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := by
        congr 1
        funext x
        exact hpt x
    _ = (c : ℂ) * ∫ x, F ((h⁻¹ : GL b k).val * x * g.val) ∂(volM ν b a) := integral_const_mul _ _
    _ = ∫ x, F x ∂(volM ν b a) := by
        rw [hT, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hkey, Complex.ofReal_one, one_mul]

end GlobalTheory.SplitWeil
