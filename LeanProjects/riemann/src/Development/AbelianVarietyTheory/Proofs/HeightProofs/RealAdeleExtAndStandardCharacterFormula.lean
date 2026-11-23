import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem pair_fst_of_snd {F : Type} [Field F] [NumberField F] (a : AF F) (h : sndA F a = 0) :
    pairA F (fstA F a) 0 = a := Prod.ext rfl h.symm

theorem half_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : Ainf F ⊗[F] E →+* ℂ)
    (a : AF F) :
    θ (fstA F (algebraMap F (AF F) (1 / 2) * a) ⊗ₜ[F] (1 : E)) = θ (fstA F a ⊗ₜ[F] (1 : E)) / 2 := by
  have h2 : algebraMap F (AF F) (1 / 2) * a + algebraMap F (AF F) (1 / 2) * a = a := by
    rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
  conv_rhs => rw [← h2, map_add, TensorProduct.add_tmul, RingHom.map_add]
  ring

theorem valTau_coe {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AF D.host.F) :
    ((valTau θ τ a : ℝ) : ℂ) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := conj_tmul_one hθ τ (fstA D.host.F a)
  exact Complex.conj_eq_iff_re.1 h

theorem real_adele_ext_and_char : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  intro D θ σ h a ha
  refine ⟨fun h0 => ?_, fun ψ hψ => ?_⟩
  · have h1 : (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = 0 := by
      refine h.ext _ ?_ fun τ => ?_
      · have e : finPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ha, TensorProduct.zero_tmul]
      · have e : infPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ← valTau_coe h.inf, h0, Complex.ofReal_zero]
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [map_zero]
    exact h1
  · have hc := hψ.2.2 θ h.inf (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a))
    rw [psiInf, pair_fst_of_snd _ (by rw [map_mul, ha, mul_zero])] at hc
    rw [hc]
    congr 1
    have e : ∀ ρ, θ ρ (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) ⊗ₜ[D.host.F] (1 : D.host.E))
        = ((valTau θ ρ a : ℝ) : ℂ) / 2 := fun ρ => by
      rw [valTau_coe h.inf]
      exact half_tmul (θ ρ) a
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.sum_div, Complex.ofReal_sum]
    push_cast
    ring

end GlobalTheory.FockCompare
