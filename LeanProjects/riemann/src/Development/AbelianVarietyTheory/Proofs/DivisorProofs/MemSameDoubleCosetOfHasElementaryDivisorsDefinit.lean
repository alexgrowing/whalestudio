import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorIndicatorMemHecke
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalCartan

theorem doubleCoset_of_hasDiv : ∀ (D : D7) [IsCMField D.host.E] (n : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (x y : UA D.host.E n), x ∈ locU n P → y ∈ locU n P →
    HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
    ∃ k₁ ∈ KP (D := D) n P, ∃ k₂ ∈ KP (D := D) n P, y = k₁ * x * k₂ := by
  intro D _ n P d x y hx hy hdx hdy
  obtain ⟨a, b, e⟩ := GlobalTheory.SphGal.HasDiv.exists_eq_mul_mul (O := Ov D.host.E P) (fun _ h => h) hdy hdx
  by_cases hs : IsSplitAt P
  · obtain ⟨φ, hφ⟩ := GlobalTheory.locU_equiv_GL D.host.E n P hs
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g := fun g => by rw [← hφ, φ.apply_symm_apply]
    refine ⟨φ.symm a, ⟨(φ.symm a).2, by rw [hc]; exact a.2⟩, φ.symm b, ⟨(φ.symm b).2, by rw [hc]; exact b.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm a * ⟨x, hx⟩ * φ.symm b := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply, hφ, hφ]
      exact e
    exact congrArg Subtype.val h
  · obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E P
      (GlobalTheory.ToricDistribution.host_unram P) hs
    obtain ⟨φ, hφ⟩ := GlobalTheory.DefU.Inert.locU_equiv D.host.E n P s hs hU.2.1
    have hc : ∀ g, cLoc P (φ.symm g : UA D.host.E n) = g.1 := fun g => by rw [← hφ, φ.apply_symm_apply]
    obtain ⟨k₁, hk₁, k₂, hk₂, e'⟩ := GlobalTheory.UnramDoubleCoset.doubleCoset_one hU _ (φ ⟨x, hx⟩).2 _ (φ ⟨y, hy⟩).2
      a a.2 b b.2 (by rw [hφ, hφ]; exact e)
    refine ⟨φ.symm ⟨k₁, hk₁.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₁.2⟩,
      φ.symm ⟨k₂, hk₂.1⟩, ⟨(φ.symm _).2, by rw [hc]; exact hk₂.2⟩, ?_⟩
    have h : (⟨y, hy⟩ : locU n P) = φ.symm ⟨k₁, hk₁.1⟩ * ⟨x, hx⟩ * φ.symm ⟨k₂, hk₂.1⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, φ.apply_symm_apply]
      exact Subtype.ext e'
    exact congrArg Subtype.val h

end GlobalTheory.LocalCartan
