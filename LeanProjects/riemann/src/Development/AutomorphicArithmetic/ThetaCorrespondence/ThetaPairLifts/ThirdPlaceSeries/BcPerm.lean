import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTyzAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open GlobalTheory.BCPerm
noncomputable section
namespace UpperTheory.GalS
theorem bcPerm_alt : _root_.GlobalTheory.BCPerm.mainTheorem := by
  intro D ht h2 h5 i x P0 PI Pa0 Pa hx hx' hB0 hB
  have hG : GalIsoN D.nd D.naut i := by
    intro P Pb hPb
    obtain ⟨ρ, hc, hss, hw, -⟩ := isoRep D ht (_root_.UpperTheory.GalS.weak' h2) i P Pb hPb
    exact ⟨ρ, hc, hss, hw⟩
  have hC : GlobalTheory.RowTie.ChebSplit D.nd := by
    intro S
    rw [dense_iff_closure_eq]
    exact h5.2.2.1 (S : Set (PlE D.host)) S.finite_toSet
  have hAN : GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := h5.2.1
  have hS := splitBC_of_galIso D.R D.host D.what₂ D.nd D.naut i hG hC hAN
  have hd0 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) ≠ 0 := by
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ (D.nd.S i : Set (PlE D.host)) ∪ (D.nd.Q i : Set (PlE D.host)) ∪
      placesOver D.host.E (D.host.g 0) ∪ placesOver D.host.E (D.host.g 1) ∪
      placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)).Finite := by
    refine (((((GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 0).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 1).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v → D.naut.locV i P0 v = D.naut.locV i PI v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => GlobalTheory.RowTie.locV_eq_of_pt D.nd D.naut i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  exact hS P0 PI hev Pa0 Pa hB0 hB
end UpperTheory.GalS
end
end
