import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicFrameLevelConjFormLevelWithCharactersStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.level_char_match : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Λ Fr h0 hh0
  obtain ⟨Fr', hFr'⟩ := GlobalTheory.T.transport_frame_along_unitary_adelic F E n cm.sig J Λ (hat F S.Lb) (gp 0 * gp 1) k h0 hh0 Fr
  obtain ⟨κ, hκ, hκU⟩ := GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Fr'
  refine ⟨h0 * κ, ?_, ?_⟩
  · intro x
    have hκi : (κ⁻¹ : UPts cm.sig J (Ad F)).1 ∈ stabGL (hat F S.Lb) := by
      simpa using (stabGL (hat F S.Lb)).inv_mem hκ
    have e : ((h0 * κ)⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x = (κ⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ ((h0⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x) := by
      rw [_root_.mul_inv_rev]; simp [Matrix.mulVec_mulVec]
    rw [e, ← hκi _, hh0]
  · intro y
    have e : ((h0 * κ)⁻¹ * y * (h0 * κ) : UPts cm.sig J (Ad F)) = κ⁻¹ * (h0⁻¹ * y * h0) * κ := by group
    obtain ⟨h1, h2⟩ := hFr' y
    obtain ⟨h3, h4⟩ := hκU (h0⁻¹ * y * h0)
    refine ⟨?_, ?_⟩
    · rw [h1, h3, e]
    · intro hy
      rw [h2]
      have hy' : ((κ⁻¹ * (h0⁻¹ * y * h0) * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U := by rw [← e]; exact hy
      rw [h4 hy']
      have hx : (⟨_, hy'⟩ : S.U) = ⟨_, hy⟩ := Subtype.ext (congrArg (fun z : UPts cm.sig J (Ad F) => z.1) e.symm)
      rw [hx]
