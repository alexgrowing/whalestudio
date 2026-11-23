import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.BlattnerShiftsSignedParameters
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LowKAddStrictAnti

open Matrix Finset Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesHermitianUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (J P P' : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' →
      Pᴴ * Formalism.REAL.Jm ε * P = J → P'ᴴ * Formalism.REAL.Jm ε * P' = J →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w,
        U (σ' (P' * g * P'⁻¹) w) = σ (P * g * P⁻¹) (U w)

namespace HermitianUnique

variable {n : ℕ} {ε : Fin n → Bool} {J P P' : Matrix (Fin n) (Fin n) ℂ}

theorem frame_mem (hP' : IsUnit P') (h : Pᴴ * Formalism.REAL.Jm ε * P = J) (h' : P'ᴴ * Formalism.REAL.Jm ε * P' = J)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) : P * g * P'⁻¹ ∈ UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP'
  have e1 : P' * P'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hg' : gᴴ * J * g = J := hg
  show (P * g * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P'⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P'⁻¹)
      = P'⁻¹ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P'⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P'⁻¹ᴴ * (P'ᴴ * Formalism.REAL.Jm ε * P') * P'⁻¹ := by rw [h, hg', h']
    _ = (P' * P'⁻¹)ᴴ * Formalism.REAL.Jm ε * (P' * P'⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e1]; simp

theorem isHCParam_of_isDS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hl : StrictAnti lam) (h : IsDS ε lam σ) :
    Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hl, fun a => ?_⟩
  obtain ⟨-, -, ⟨⟨h1, -⟩, -, -⟩, -, -, ⟨S, -, -, -, ⟨v, -, hv0, hv⟩, -⟩, -⟩ := h
  obtain ⟨m, hm⟩ := GlobalTheory.DiscreteSeriesTest.wt_int (ε := ε) (μ := PI.UpqRep.lowK ε lam) h1 hv0 hv a
  have h2 := GlobalTheory.DiscreteSeriesTest.lowK_add ε lam a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, PI.UpqRep.rhoC] at h2
  refine ⟨m + (univ.filter fun b => a < b ∧ ε b = ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card
    - (n - 1) + a, ?_⟩
  push_cast
  linarith

end HermitianUnique

open HermitianUnique in

theorem discreteSeriesHermitianUnique_iff : DiscreteSeriesHermitianUnique ↔ DiscreteSeriesUpqUnique := by
  constructor
  · intro h n ε lam hl H H' _ _ _ _ σ σ' hσ hσ'
    obtain ⟨U, hU⟩ := h n ε lam hl (Formalism.REAL.Jm ε) 1 1 isUnit_one isUnit_one (by simp) (by simp) H' H σ' σ hσ' hσ
    refine ⟨U, fun g hg v => ?_⟩
    simpa using hU g hg v
  · intro h n ε lam hl J P P' hP hP' hJ hJ' H H' _ _ _ _ σ σ' hσ hσ'
    obtain ⟨U, hU⟩ := h n ε lam hl H' H σ' σ hσ' hσ
    obtain ⟨-, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
    have e : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
    have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
    have e' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP')
    have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH J := by
      show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J * 1 = J
      simp
    have ha : P * 1 * P'⁻¹ ∈ UJset ε := frame_mem hP' hJ hJ' one
    have hb : P' * 1 * P⁻¹ ∈ UJset ε := frame_mem hP hJ' hJ one
    rw [Matrix.mul_one] at ha hb
    have hsurj : Function.Surjective
        (⟨(σ (P * P'⁻¹) : H →ₗ[ℂ] H), hiso _ ha⟩ : H →ₗᵢ[ℂ] H) := by
      intro v
      refine ⟨σ (P' * P⁻¹) v, ?_⟩
      have e3 : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, e', Matrix.one_mul, e2]
      have := hmul _ ha _ hb
      rw [e3, h1] at this
      exact (congrArg (fun T : H →L[ℂ] H => T v) this).symm
    refine ⟨U.trans (LinearIsometryEquiv.ofSurjective _ hsurj), fun g hg w => ?_⟩
    show σ (P * P'⁻¹) (U (σ' (P' * g * P'⁻¹) w)) = σ (P * g * P⁻¹) (σ (P * P'⁻¹) (U w))
    have hg' := frame_mem hP' hJ' hJ' hg
    have hg1 := frame_mem hP hJ hJ hg
    have k1 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ ha _ hg')
    have k2 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ hg1 _ ha)
    have k3 : P * P'⁻¹ * (P' * g * P'⁻¹) = P * g * P⁻¹ * (P * P'⁻¹) := by
      calc P * P'⁻¹ * (P' * g * P'⁻¹) = P * (P'⁻¹ * P') * g * P'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P * g * (P⁻¹ * P) * P'⁻¹ := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
        _ = P * g * P⁻¹ * (P * P'⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hU _ hg']
    rw [k3] at k1
    exact k1.symm.trans k2

theorem discreteSeriesHermitianUnique_of_classification (h : GlobalTheory.DSId.DSClass) : DiscreteSeriesHermitianUnique :=
  discreteSeriesHermitianUnique_iff.2 (discreteSeriesUpqUnique_of_classification h)

theorem DiscreteSeriesHermitianUnique.exists_intertwiner (h : DiscreteSeriesHermitianUnique) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M M' : DSModel V S) :
    ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w) := by
  have key : ∀ τ, ∃ U : M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U (M'.rep τ g w) = M.rep τ g (U w) := by
    intro τ
    obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) (M'.enum τ)
    exact h _ (M.ε τ) (M.lam τ) (HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) (M'.fr τ)
      (M.fr_unit τ) (M'.fr_unit τ) (M.fr_gram τ) (he ▸ M'.fr_gram τ) _ _ (M.σ τ) (M'.σ τ) (M.ds τ)
      (hl ▸ he ▸ M'.ds τ)
  choose U hU using key
  exact ⟨U, hU⟩

theorem DiscreteSeriesUpqUnique.exists_intertwiner (h : DiscreteSeriesUpqUnique) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M M' : DSModel V S) :
    ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w) :=
  (discreteSeriesHermitianUnique_iff.2 h).exists_intertwiner M M'

end GlobalTheory.Published
