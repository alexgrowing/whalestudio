import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeierstrassPSeriesAndSigmaStarQuotientSeriStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformisesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeriesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Param

open PowerSeries

theorem isWpSer_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (f a) (f b) (PowerSeries.map f P) := by
  have hd : derivativeFun (PowerSeries.map f P) = PowerSeries.map f (derivativeFun P) := by
    ext n
    simp [derivativeFun, coeff_derivative]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.1, map_one]
  · have := congrArg (PowerSeries.map f) h.2
    simp only [map_pow, map_sub, map_mul, map_C, map_X, map_ofNat] at this
    rw [hd]
    exact this

theorem isWpSer_rescale {K : Type*} [CommRing K] (e : K) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (e ^ 4 * a) (e ^ 6 * b) (rescale e P) := by
  have hd : X * derivativeFun (rescale e P) = rescale e (X * derivativeFun P) := by
    ext n
    cases n with
    | zero => simp [coeff_rescale]
    | succ n => simp [coeff_rescale, coeff_succ_X_mul, derivativeFun, coeff_derivative, mul_assoc, pow_succ']
  have hC : ∀ c : K, rescale e (C c) = C c := by
    intro c
    ext n
    cases n <;> simp [coeff_rescale, coeff_C]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, h.1]
    simp
  · have := congrArg (rescale e) h.2
    rw [hd]
    rw [map_pow, map_sub] at this
    simp only [map_pow (rescale e), map_sub (rescale e), map_mul (rescale e) _ P, map_mul (rescale e) (C _),
      map_mul (rescale e) 4, hC, rescale_X, map_ofNat] at this
    rw [this]
    simp only [map_mul, map_pow]
    ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem theta_series_map_coefficients (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (T : PowerSeries Qbar)
    (h : PowerSeries.mk (coef1 F) = PowerSeries.map (algebraMap Qbar ℂ) T) :
    GL3Theta.ser1 lam F = PowerSeries.map lam T := by
  ext n
  have := congrArg (coeff n) h
  rw [coeff_mk, coeff_map] at this
  rw [GL3Theta.ser1, coeff_mk, coeff_map, ← lamC_coe']
  exact congrArg (lamC lam) this

theorem invariants (g : GL3Theta.G1 p) (a b : Qbar) (ha : g2 g.abelian₂ = a) (hb : g3 g.abelian₂ = b) :
    g.W.c₄ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * g.lam a ∧
    g.W.c₆ / 216 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * g.lam b ∧
    g.W.b₂ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r := by
  have e : ∀ x : Qbar, lamC g.lam (-(x : ℂ) / 4) = -g.lam x / 4 := by
    intro x
    have : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast; rfl
    rw [this, lamC_coe', map_div₀, map_neg, map_ofNat]
  unfold GL3Theta.G1.W
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆,
    WeierstrassCurve.variableChange_b₂]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, wModel, ha, hb, e]
  refine ⟨by ring, by ring, by ring⟩

theorem exists_algebraic_series (Λ : AddSubgroup ℂ) (hL : IsLat Λ) (a b w : Qbar) (ha : g2 Λ = a) (hb : g3 Λ = b)
    (hσ : AlgEnt (sgStar Λ)) (v : ℂ) (hv : v ∉ Λ) (hw : wpF Λ v = w) :
    ∃ P₀ S : PowerSeries Qbar, IsWpSer a b P₀ ∧
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) ∧
      PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.map (algebraMap Qbar ℂ) (S ^ 2 * lineSer P₀ w) := by
  obtain ⟨P, hP, hPv⟩ := GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries Λ hL
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.T.existsUnique_isWeierstrassPSeries Qbar a b
  rw [ha, hb] at hP
  have hPP : P = PowerSeries.map (algebraMap Qbar ℂ) P₀ :=
    (GlobalTheory.T.existsUnique_isWeierstrassPSeries ℂ a b).unique hP (isWpSer_map (algebraMap Qbar ℂ) hP₀)
  have h0 : coef1 (sgStar Λ) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar Λ) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  refine ⟨P₀, S, hP₀, hS, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
  rw [hPv v hv, hS, hPP, hw]
  simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  have : algebraMap Qbar ℂ w = (w : ℂ) := rfl
  rw [this]
  ring

theorem subst_lineSer {K : Type*} [Field K] (l E q S P : PowerSeries K) (ε r w : K) (hl0 : constantCoeff l = 0)
    (hE : X * E = l * subst (C ε * l) S)
    (hform : X ^ 2 * (subst l (rescale ε P) : PowerSeries K) = l ^ 2 * lineSer q (-(ε ^ 2 * r))) :
    (subst (C ε * l) (S ^ 2 * lineSer P w) : PowerSeries K) = E ^ 2 * lineSer q (ε ^ 2 * (w - r)) := by
  have hl : HasSubst l := HasSubst.of_constantCoeff_zero' hl0
  have hel : HasSubst (C ε * l) := HasSubst.of_constantCoeff_zero' (by simp [hl0])
  have hres : subst l (rescale ε P) = (subst (C ε * l) P : PowerSeries K) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' ε) hl, subst_smul hl, subst_X hl, smul_eq_C_mul]
  rw [hres] at hform
  have hCs : subst (C ε * l) (C w : PowerSeries K) = (C w : PowerSeries K) := by
    rw [← coe_substAlgHom hel]
    exact (substAlgHom hel).commutes w
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := K)))
  rw [← mul_assoc, ← mul_pow, hE]
  simp only [lineSer, map_mul, map_pow, map_sub, map_neg] at hform ⊢
  rw [subst_mul hel, subst_pow hel, subst_sub hel, subst_mul hel, subst_pow hel, subst_X hel, hCs]
  linear_combination (subst (C ε * l) S : PowerSeries K) ^ 2 * hform

theorem constantCoeff_l (g : GL3Theta.G1 p) : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, GL3Theta.G1.l, flog, coeff_mk]; simp

theorem X_mul_ePhi1 (g : GL3Theta.G1 p) (S : PowerSeries ℂ_[p]) (hS : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * S) :
    X * ePhi1 g.lam g.abelian₂ g.C g.wq = g.l * subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) S := by
  have hl0 := constantCoeff_l g
  have hel : HasSubst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl0, mul_zero])
  have hS' : sgSer g.lam g.abelian₂ = X * S := hS
  ext n
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, hl0,
      constantCoeff_X, zero_mul, zero_mul]
  | succ n =>
    rw [coeff_succ_X_mul, ePhi1, coeff_mk, hS', ← C_eq_algebraMap, ← GL3Theta.G1.W, ← GL3Theta.G1.l,
      subst_mul hel, subst_X hel, mul_assoc, coeff_C_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem sqTh_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨a, ha⟩ : ∃ a : Qbar, g2 g.abelian₂ = a := ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Qbar, g3 g.abelian₂ = b := ⟨⟨_, h3⟩, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w : Qbar, wpF g.abelian₂ v = w := ⟨⟨_, hw⟩, rfl⟩
  obtain ⟨P₀, S, hP₀, hS, hT⟩ := exists_algebraic_series g.abelian₂ hL a b w ha hb hσ v hv hw'
  refine ⟨⟨hL.differentiable_sqTh v, fun n => ?_⟩, ?_⟩
  · have := congrArg (coeff n) hT
    rw [coeff_mk, coeff_map] at this
    rw [this]
    exact SetLike.coe_mem _
  obtain ⟨i4, i6, i2⟩ := invariants g a b ha hb
  have hform := GlobalTheory.T.weierstrassP_formalGroupLog_uniformises p g.W g.wq
    (rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (PowerSeries.map g.lam P₀)) hq
    (by rw [i4, i6]; exact isWpSer_rescale _ (isWpSer_map g.lam hP₀))
  rw [i2, ← GL3Theta.G1.l] at hform
  have hE := X_mul_ePhi1 g (PowerSeries.map g.lam S) (by rw [theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X])
  have hm : PowerSeries.map g.lam (S ^ 2 * lineSer P₀ w) =
      PowerSeries.map g.lam S ^ 2 * lineSer (PowerSeries.map g.lam P₀) (g.lam w) := by
    simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  rw [GL3Theta.G1.atU, ← C_eq_algebraMap, theta_series_map_coefficients g.lam _ _ hT, hm, xAt, hw', lamC_coe']
  exact subst_lineSer _ _ _ _ _ _ _ _ (constantCoeff_l g) hE hform

end GlobalTheory.EvenTheta.Param
