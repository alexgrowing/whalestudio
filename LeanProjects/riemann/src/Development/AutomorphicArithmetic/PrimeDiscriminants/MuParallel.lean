import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

noncomputable section

namespace UpperTheory.Host

open Formalism.BasicNotions NumberField

variable {R : Ranks} (H : Host R)

def psiEquiv : R.Psi ≃ (H.E ≃ₐ[H.K] H.E) where
  toFun g :=
    { (H.sigmaOf (g : R.GG) : H.E ≃+* H.E) with
      commutes' := fun x => by
        have h1 : H.sigmaOf (g : R.GG) H.sqd = H.sqd :=
          (H.galE_mem_Psi_iff _).1 (by rw [show H.galE (H.sigmaOf (g : R.GG)) = g from H.gal.apply_symm_apply _]; exact g.2)
        have h2 : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf (g : R.GG))) := by
          refine IntermediateField.adjoin_simple_le_iff.2 ?_
          rw [IntermediateField.mem_fixedField_iff]
          intro f hf
          exact (Subgroup.zpowers_le.2 (show H.sigmaOf (g : R.GG) ∈ MulAction.stabilizer _ H.sqd from h1)) hf
        exact (IntermediateField.mem_fixedField_iff _ _).1 (h2 x.2) _ (Subgroup.mem_zpowers _) }
  invFun σ := ⟨H.gal (σ.restrictScalars ℚ), (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, H.sqd_mem_K⟩)⟩
  left_inv g := Subtype.ext (H.gal.apply_symm_apply (g : R.GG))
  right_inv σ := AlgEquiv.ext fun x => by
    show H.gal.symm (H.gal (σ.restrictScalars ℚ)) x = σ x
    rw [MulEquiv.symm_apply_apply]
    rfl

theorem prod_sigmaOf [Fintype R.Psi] (x : H.E) :
    ∏ g : R.Psi, H.sigmaOf (g : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.hostE_isGalois
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv (psiEquiv H) _ _ fun g => rfl

theorem mu_one [Fintype R.Psi] : UpperTheory.MU (fun g : R.Psi => H.emb (g : R.GG)) (fun _ => 1) := by
  intro z hz
  have h1 : ∀ g : R.Psi, H.emb (g : R.GG) z ^ (1 : ℤ) = H.φ₀ (H.sigmaOf (g : R.GG) z) := fun g => zpow_one _
  simp only [h1]
  rw [← map_prod, prod_sigmaOf, H.der.norm_mu z hz, map_one, map_one]

theorem muQ_const [Fintype R.Psi] {e : R.Psi → ℚ} {c : ℤ} (h : ∀ g, e g = c) :
    UpperTheory.MUQ (fun g : R.Psi => H.emb (g : R.GG)) e :=
  ⟨fun _ => c, h, (mu_one H).const c⟩

end UpperTheory.Host

end
