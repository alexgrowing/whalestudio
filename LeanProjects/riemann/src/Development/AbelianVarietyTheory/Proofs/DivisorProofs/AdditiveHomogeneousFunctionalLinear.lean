import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelCoordinatesRationalSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactorAltBis

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
open scoped Classical

namespace GlobalTheory.ThetaUniq

theorem unique_of_ratInv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ L : Fn F n d → ℂ, (∀ Ψ ∈ schA F (Fin n × Fin d), ∀ Ψ' ∈ schA F (Fin n × Fin d), L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), L (c • Ψ) = c * L Ψ) →
      (∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
        ∀ f : SInf F (Fin n × Fin d), L (pureA F f g) = T f) →
      (∀ x : Matrix (Fin n) (Fin d) E, ∀ Ψ ∈ schA F (Fin n × Fin d), L (M.co.rho B.ψ (incM F x) Ψ) = L Ψ) →
      ∃ c : ℂ, ∀ Ψ ∈ schA F (Fin n × Fin d), L Ψ = c * thetaSum F Ψ := by
  intro _ F E _ _ _ _ _ σ B n d X W M hB hM _ L hadd hsmul hadm hinv
  have hψ : IsStd B.ψ := hB.std
  have hschr : ∀ y z : Fin n × Fin d → F, ∀ Ψ ∈ schA F (Fin n × Fin d),
      L (schr B.ψ ((fun i => algebraMap F (AF F) (y i)), (fun i => algebraMap F (AF F) (z i))) Ψ) = L Ψ := by
    intro y z Ψ hΨ
    obtain ⟨x, hx⟩ := GlobalTheory.T.model_coordinates_rational_surjective F E σ B n d X W M hB hM y z
    have h := hinv x Ψ hΨ
    rw [Darboux.rho, hx] at h
    exact h
  have htr : ∀ ξ : Fin n × Fin d → F, ∀ Ψ ∈ schA F (Fin n × Fin d),
      L (fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i))) = L Ψ := by
    intro ξ Ψ hΨ
    have h := hschr ξ 0 Ψ hΨ
    have e : schr B.ψ ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i))) Ψ
        = fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i)) := by
      funext x
      simp [schr]
    rw [e] at h
    exact h
  have hmod : ∀ z : Fin n × Fin d → F, ∀ Ψ ∈ schA F (Fin n × Fin d),
      L (fun x => B.ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * Ψ x) = L Ψ := by
    intro z Ψ hΨ
    have h := hschr 0 z Ψ hΨ
    have e : schr B.ψ ((fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)), (fun i => algebraMap F (AF F) (z i))) Ψ
        = fun x => B.ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) * Ψ x := by
      have h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) = 0 := by funext i; simp
      funext x
      rw [h0]
      simp [schr]
    rw [e] at h
    exact h
  exact GlobalTheory.T.translation_invariant_functional_schwartz F (Fin n × Fin d) L hadd hsmul htr
    (GlobalTheory.T.schwartz_functional_archimedean_factor_alt F (Fin n × Fin d) B.ψ hψ L hadd hsmul hadm htr hmod)

end GlobalTheory.ThetaUniq
