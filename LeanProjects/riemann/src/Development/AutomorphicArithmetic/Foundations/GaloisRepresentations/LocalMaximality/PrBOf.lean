import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedDualRegularFormsFiniteCoverStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.prB_of :
    GoodZ → PrB := by
  intro hG F K _ _ _ _ _ _ d x h τ hτ ρ hρ a q had hqd e he y hy
  have mono : ∀ r : ℕ, ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) r ≤ omB ℂ K (rB ℂ K (xv x) t) r :=
    fun r => (hG F K d x h r).2.2
  have hvan : ∀ i, (Finset.univ.erase i).Nonempty →
      ∀ u ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) (d - a),
      ∀ v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a,
      (LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ) u v = 0 := by
    intro i hi u hu v hv
    have hvq : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
    have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) h τ hτ (Finset.univ.erase i) hi (d - a) a
      (by omega) v hvq).2 hv u hu
    exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) h.pd ρ hρ i _ hi (Finset.notMem_erase i _) _ hmem
  obtain ⟨ε, hε⟩ := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a))
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))
    (mono _) (mono _) hvan ((d : ℤ) - (q : ℕ))
  obtain ⟨y', hy', rfl⟩ := hy
  have key := hε e he.1 y' (by
    have e1 : (d : ℤ) - ((d : ℤ) - (q : ℕ)) - 1 = (q : ℤ) - 1 := by ring
    rw [e1]
    exact hy')
  have h0 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a)).D e = 0 := he.2
  rw [h0, map_zero, LinearMap.zero_apply] at key
  exact (smul_eq_zero_iff_eq ε).1 key.symm
