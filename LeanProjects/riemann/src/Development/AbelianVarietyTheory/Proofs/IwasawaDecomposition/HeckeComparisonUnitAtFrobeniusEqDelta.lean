import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem cHkT_eq_of_isFrob : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  intro D T i b P hP σ hσ
  have hA := D.nd.plOm.2 P
  have key : ∀ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ →
      T.delta i τ = T.delta i σ := by
    intro τ hτ
    have hmem := inv_mul_mem_Ine_of_isFrob hσ hτ
    have h1 : T.delta i (σ⁻¹ * τ) = 1 := by
      by_contra hne
      exact hP (T.primes_subset_exceptional i ((T.delta_ram i P _ hA).1 ⟨_, hmem, hne⟩))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  unfold cHkT
  rw [dif_pos ⟨σ, hσ⟩, key _ (Exists.choose_spec (⟨σ, hσ⟩ : ∃ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ))]

end GlobalTheory.HeightCounting.FormsStep
