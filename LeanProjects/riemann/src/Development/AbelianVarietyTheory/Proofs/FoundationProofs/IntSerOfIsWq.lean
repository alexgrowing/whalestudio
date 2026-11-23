import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dif_pos (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
