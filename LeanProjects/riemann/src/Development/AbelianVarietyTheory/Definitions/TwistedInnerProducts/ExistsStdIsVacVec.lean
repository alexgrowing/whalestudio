import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (M : DSModel V S) (M' : DSModel W S') :
    ∃ f, IsVacVec ψ θ M M' f :=
  VacVec.exists_isVacVec ψ θ M M' hψ hθ

theorem exists_std_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') :
    ∃ ψ θ f, IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ IsVacVec ψ θ M M' f :=
  VacVec.exists_char_fam_isVacVec M M'

theorem not_isVacVec_zero {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') : ¬ IsVacVec ψ θ M M' 0 := fun h => h.ne rfl

theorem exp_of_even {k : Fin D.R.m} (hk : Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k - 1 / 2 ∧ expT D k τ = -(D.hc τ).e k := by
  simp [expS, expT, hk]

theorem exp_of_odd {k : Fin D.R.m} (hk : ¬ Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k ∧ expT D k τ = -(D.hc τ).e k - 1 / 2 := by
  simp [expS, expT, hk]

theorem hasInfExp_div {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η⁻¹) τ (a - b) := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  refine ⟨n - m, by push_cast; rw [hn, hm]; ring, h1, fun θ hθ x hx hτ => ?_⟩
  have e1 := h2 θ hθ x hx hτ
  have e2 := h3 θ hθ x hx hτ
  set z : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hz
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, e1, e2]
  by_cases h0 : z = 0
  · have a1 : n = 0 := by
      by_contra h; exact (χ x).coe_ne_zero (by rw [e1, h0, zero_zpow _ h])
    have a2 : m = 0 := by
      by_contra h; exact (η x).coe_ne_zero (by rw [e2, h0, zero_zpow _ h])
    simp [a1, a2]
  · rw [zpow_sub₀ h0, div_eq_mul_inv]

theorem isHeckeChar_div {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2]; simp⟩

theorem exists_isStepWeil (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (k : Fin D.R.m)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (V W : HSp D)
    (hV : V.rank % 2 = ((k : ℕ) + 1) % 2) (hW' : W.rank % 2 = (k : ℕ) % 2)
    (μ η : (AE D)ˣ →* Circle) (hμ : IsHeckeChar D μ) (hμe : ∀ τ, HasInfExp D μ τ (-(D.hc τ).e k)) (hμr : ResEta D μ 0)
    (hη : IsHeckeChar D η) (hηe : ∀ τ, HasInfExp D η τ (1 / 2)) (hηr : ResEta D η 1) :
    ∃ ω, IsStepWeil k ψ V W ω := by
  have hq := isHeckeChar_div hμ hη
  have hqr : ResEta D (μ * η⁻¹) (0 + 1) := resEta_mul hμr (resEta_inv hηr)
  by_cases hk : Even (k : ℕ)
  · have hk' := Nat.even_iff.1 hk
    obtain ⟨ω, hω⟩ := hW D ψ V W (μ * η⁻¹) μ hψ hq hμ (resEta_parity hqr (by omega)) (resEta_parity hμr (by omega))
    refine ⟨ω, _, _, hω, fun τ => ?_⟩
    rw [(exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div (hμe τ) (hηe τ), hμe τ⟩
  · have hk' := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hk)
    obtain ⟨ω, hω⟩ := hW D ψ V W μ (μ * η⁻¹) hψ hμ hq (resEta_parity hμr (by omega)) (resEta_parity hqr (by omega))
    refine ⟨ω, _, _, hω, fun τ => ?_⟩
    rw [(exp_of_odd hk τ).1, (exp_of_odd hk τ).2]
    exact ⟨hμe τ, hasInfExp_div (hμe τ) (hηe τ)⟩

theorem rank_parity (D : D7) (k : ℕ) :
    (D.R.r + k * D.R.t) % 2 = (k + 1) % 2 ∧ (D.R.r + (k + 1) * D.R.t) % 2 = k % 2 := by
  have h1 := Nat.odd_iff.1 (r_odd D)
  have h2 := Nat.odd_iff.1 D.R.t_odd
  constructor <;> rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.add_mod, Nat.mul_mod, h, h1, h2]

example : signed [1] [2] (1 / 2) = {(3 / 2, true), (5 / 2, false)} := by
  simp [signed]; norm_num

end GlobalTheory.Chain

end
