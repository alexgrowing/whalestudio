import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Letter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication

noncomputable section

namespace CompanionTheory.LimBd.Main

open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace

theorem beta_at_infinity_zero : BetaInfZero := by
  intro k r Wp Wq _ _ _ _ _ _ D F F' h
  unfold B.betaInf B.betaInfTau
  refine integral_eq_zero_of_ae ?_
  filter_upwards [P.B5.ae_inSS D] with p hp
  have hχ : ∀ t, D.χ t ≠ 0 → t ≠ 0 := fun t ht h0 => by
    have := (D.χ_supp (subset_tsupport _ ht)).1
    rw [h0] at this
    norm_num at this
  have h0 : B.regBracket D F F' p = fun _ _ => 0 := by
    funext t₁ t₂
    unfold B.regBracket
    by_cases h1 : D.χ t₁ = 0
    · simp [h1]
    by_cases h2 : D.χ t₂ = 0
    · simp [h2]
    rw [h (B.dilation₂ (t₁, t₂) p) ⟨hp.1, P.B5.dil_mem_N t₁ (hχ _ h1) hp.2.1, hp.2.2.1,
      P.B5.dil_mem_N t₂ (hχ _ h2) hp.2.2.2⟩, mul_zero]
  simp [h0, B.oneMinusDD]

theorem inner_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ) {a g b : B.Mat k r} (ha : a ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) (v w : H) :
    ⟪w, σ (a * g * b) v⟫_ℂ = ⟪σ a⁻¹ w, σ g (σ b v)⟫_ℂ := by
  obtain ⟨hu, hai, hm⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a : H →ₗ[ℂ] H), hσ.2.1 a ha⟩
  have e : σ a (σ a⁻¹ w) = w := by
    have := hσ.1.2 a ha _ hai
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  rw [hσ.1.2 _ (hm g hg) b hb, hσ.1.2 a ha g hg, ← L.inner_map_map (σ a⁻¹ w)]
  show _ = ⟪σ a (σ a⁻¹ w), _⟫_ℂ
  rw [e]
  rfl

theorem phase_zero_alt : PhZero := by
  intro hE k r Wp Wq _ _ _ _ _ _ D ε μ μ' φ φ' T T' hφ hφ' hne p hp
  obtain ⟨H, i1, i2, i3, σ, v, w, hμ, hσ, -, -, hφG⟩ := hφ
  obtain ⟨H', j1, j2, j3, σ', v', w', hμ', hσ', -, -, hφG'⟩ := hφ'
  have hR := isURepOn_of_ds hσ
  have grp := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r
  set a : B.Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with ha'
  set b : B.Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hb'
  have ha : a ∈ UH (Hpk k r) := (grp _ (grp _ hp.1.1).2.1).2.2 _ (grp _ hp.2.1.1).2.1
  have hb : b ∈ UH (Hpk k r) := (grp _ hp.2.2.2.1).2.2 _ hp.2.2.1.1
  have hμG : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) D.μG :=
    ⟨P.B5.haar_sigmaFinite D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩
  have hz := (schur_inequiv hσ hσ' (capelli_inequivalence hE k r ε ε μ μ' H H' σ σ' hμ hμ' hσ hσ' hne) hμG
    (σ b v) (σ a⁻¹ w) v' w').2
  set S : Wq →L[ℂ] Wp := (D.π (Matrix.of p.1.1)).comp (T.comp (D.π' (Matrix.of p.2.1)⁻¹))
  unfold B.Ph
  rw [← zero_mul (B.hsInner S T'), ← hz, ← integral_mul_const]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  filter_upwards [hae] with g hg
  have e1 : B.sgs p (Matrix.of g) = a * Matrix.of g * b := by
    simp only [B.sgs, ha', hb', Matrix.mul_assoc]
  have hm : a * Matrix.of g * b ∈ UH (Hpk k r) := (grp _ ((grp _ ha).2.2 _ hg)).2.2 _ hb
  have e2 : B.rho D p (fun g => φ g • T) (Matrix.of g) = φ (a * Matrix.of g * b) • S := by
    simp only [B.rho, e1, S, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  rw [e2, P.B6.hsInner_smul_left, P.B6.hsInner_smul_right, hφG _ hm, hφG' _ hg, inner_translate hR ha hg hb,
    ← mul_assoc]
  rfl

end CompanionTheory.LimBd.Main
