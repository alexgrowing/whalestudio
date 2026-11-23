import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SheafCycle

theorem interNum_nonneg_of_interNumRed_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, (P i).IsLB) → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) = (d : ℕ) → 0 ≤ interNumRed k Z P) → 0 ≤ interNum k F P := by
  intro k _ _ X _ hX d F _ hF P hP hZ
  haveI : NoetherianSpace X := by
    obtain ⟨N, i, hi, hc⟩ := hX
    haveI : LocallyOfFiniteType (i ≫ PSpace.str k N) := inferInstance
    haveI : QuasiCompact (i ≫ PSpace.str k N) := inferInstance
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str k N)
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str k N)
    haveI : IsNoetherian X := {}
    infer_instance
  obtain ⟨C, hCfin, hCirr, hCeq⟩ :=
    NoetherianSpace.exists_finite_set_closeds_irreducible (⟨support F, isClosed_support F⟩ : Closeds X)
  have hT : {w : X | w ∈ support F ∧ topologicalKrullDim (closure {w} : Set X) = (d : WithBot ℕ∞)}.Finite := by
    refine (hCfin.biUnion fun t _ => (show ({x : X | IsGenericPoint x (t : Set X)}).Subsingleton from
      fun a ha b hb => ha.eq hb).finite).subset ?_
    rintro w ⟨hw, hwd⟩
    have hw' : w ∈ ((sSup C : Closeds X) : Set X) := by rw [← hCeq]; exact hw
    rw [Closeds.coe_sSup, Set.sUnion_image,
      (hCfin.isClosed_biUnion fun t _ => t.isClosed).closure_eq, Set.mem_iUnion₂] at hw'
    obtain ⟨t, ht, hwt⟩ := hw'
    obtain ⟨g, hg⟩ := QuasiSober.sober (hCirr t ht) t.isClosed
    have hgs : g ∈ support F := by
      have : (t : Set X) ⊆ support F := by
        have h1 : t ≤ sSup C := le_sSup ht
        rw [← hCeq] at h1
        exact h1
      exact this hg.mem
    have hwg : w ∈ closure {g} := by
      have hcl' : closure ({g} : Set X) = t := hg
      rw [hcl']; exact hwt
    have := eq_of_mem_closure hF hwd g hgs hwg
    subst this
    exact Set.mem_biUnion ht hg
  rw [interNum_eq_sum_length_mul_interNumRed k X hX (Fin d) P hP F (by simpa using hF) hT.toFinset
    (fun w hw hwd => by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hw, by simpa using hwd⟩)]
  refine Finset.sum_nonneg fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  refine mul_nonneg (by positivity) (hZ _ isIrreducible_singleton.closure hw.2)

end GlobalTheory.SheafCycle
