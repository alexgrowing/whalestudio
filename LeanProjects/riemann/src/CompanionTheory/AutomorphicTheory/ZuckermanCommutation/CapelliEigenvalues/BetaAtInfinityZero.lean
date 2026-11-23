import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.SchurH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Matrix PI.UpqRep Formalism.FourierDecayAlt MeasureTheory CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

theorem kfin_iff (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : B.Mat k r) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) (hP : IsCayleyU k r ε P) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hP.2)
  have hPi : P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hinv ▸ Unitary.star_mem hP.2
  constructor
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun g hg x hx => hst _ ⟨back_mem hP.1 ?_, ?_⟩ x hx⟩
    · show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPi hg.1) hP.2
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun x hx y hy => ?_⟩
    have hu : P * x * P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hx.2) hPi
    have hJ : (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε := forth_mem hP.1 hx.1
    have h1 : (P * x * P⁻¹) * (P * x * P⁻¹)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    have hK : P * x * P⁻¹ ∈ Kset ε := by
      refine ⟨hu, ?_⟩
      generalize P * x * P⁻¹ = g at hJ h1
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [h1, Matrix.one_mul]
    have := hst _ hK y hy
    simpa only [back_forth hP.1] using this

theorem eq_of_capelliPolynomial_eq {n : ℕ} {μ μ' : Fin n → ℝ} (hμ : StrictAnti μ) (hμ' : StrictAnti μ')
    (h : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (μ' s : ℂ)) Y) : μ = μ' := by
  have key : ∀ {a b : Fin n → ℝ}, (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y =
      Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) → Set.range a ⊆ Set.range b := by
    rintro a b hab _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hab] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨t, ?_⟩
    have : ((b t : ℝ) : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  exact (hμ.range_inj hμ').1 (Set.Subset.antisymm (key h) (key fun Y => (h Y).symm))

theorem capelli_inequivalence : Inequiv := by
  intro hE k r ε ε' μ μ' H H' _ _ _ _ _ _ σ σ' hμ hμ' hσ hσ' hne
  rintro ⟨U, hU⟩
  apply hne
  obtain ⟨P, hP, hds⟩ := id hσ
  obtain ⟨S, hS, hSK, -, ⟨v, hvS, hv0, -⟩, -⟩ := hds.2.2.2.2.2.1
  have hv : IsKFinHpk (k := k) (r := r) σ v := (kfin_iff k r ε P H σ v hP).2 ⟨S, hS, hvS, hSK⟩
  have hv' : IsKFinHpk (k := k) (r := r) σ' (U v) := by
    obtain ⟨S₁, h1, h2, h3⟩ := hv
    refine ⟨S₁.map (U.toLinearEquiv : H →ₗ[ℂ] H'), inferInstance, Submodule.mem_map_of_mem h2, ?_⟩
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, h3 g hg x hx, hU g hg.1 x⟩
  have c1 : IsCoef k r ε μ (fun g => ⟪v, σ g v⟫_ℂ) := ⟨H, _, _, inferInstance, σ, v, v, hμ, hσ, hv, hv, fun _ _ => rfl⟩
  have c2 : IsCoef k r ε' μ' (fun g => ⟪v, σ g v⟫_ℂ) :=
    ⟨H', _, _, inferInstance, σ', U v, U v, hμ', hσ', hv', hv', fun g hg => by
      rw [← hU g hg v, U.inner_map_map]⟩
  have h1G : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  have hσ1 : σ 1 = 1 := (isURepOn_of_ds hσ).1.1
  refine eq_of_capelliPolynomial_eq hμ.1 hμ'.1 fun Y => ?_
  have e1 := hE k r ε μ _ ℂ ℂ 1 c1 Y 1 h1G
  have e2 := hE k r ε' μ' _ ℂ ℂ 1 c2 Y 1 h1G
  rw [e1] at e2
  have e3 := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) e2
  simp only [hσ1, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one] at e3
  exact mul_right_cancel₀ (inner_self_ne_zero.2 hv0) e3

end CompanionTheory.CapEig

end
