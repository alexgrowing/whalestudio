import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem splitClosed_of_isGrpPullback_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' G₁ : Over (Sp R)}
    [GrpObj G'] [GrpObj G₁] {φ : G₁.left ⟶ G'.left} (hφ : IsGrpPullback G₁ G' (𝟙 _) φ) (h : SplitClosed G') :
    SplitClosed G₁ := by
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := h
  let t := thick R (maximalIdeal R) 0
  have h2 := (isGrpPullback_pullback G₁ t).comp hφ
  have h3 := isGrpPullback_pullback G' t
  let ψ : (thickObj R (maximalIdeal R) 0 G₁).left ⟶ (thickObj R (maximalIdeal R) 0 G').left :=
    pullback.lift (pullback.fst G₁.hom t ≫ φ) (pullback.snd G₁.hom t) (by
      rw [Category.assoc, hφ.1.w, Category.comp_id, pullback.condition])
  have hc : IsGrpPullback (thickObj R (maximalIdeal R) 0 G₁) (thickObj R (maximalIdeal R) 0 G') (𝟙 _) ψ :=
    IsGrpPullback.cancel h3 (h2.congr (by rw [Category.comp_id, Category.id_comp]) (pullback.lift_fst _ _ _).symm)
      (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
  obtain ⟨Q', -⟩ := GlobalTheory.UU.exists_tq_baseChange _ _ (𝟙 _) X _ _ ψ hc Q
  exact ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q'⟩⟩

noncomputable section

theorem exists_finExt_splitClosed_twoTorsRat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  intro R _ _ _ hR G _ _ hG A gen hgen
  obtain ⟨K', _, _, hK'fin, H⟩ := GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks R G A gen hgen
  haveI : IsDiscreteValuationRing R := hR.1
  haveI : IsAdicComplete (maximalIdeal R) R := hR.2.1
  haveI : CharZero R := hR.2.2
  haveI : CharZero (FractionRing R) := (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R _) |>.1 inferInstance
  obtain ⟨W, _, _, _, hWc, _, _, _, hc, hWfin, hWinj, hWloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) K'
  haveI : CharZero W := (algebraMap R W).charZero_iff hWinj |>.1 inferInstance
  have hWd : GlobalTheory.LN.CDvr W := ⟨inferInstance, hWc, inferInstance⟩
  have hGW : IsSemiAbelian ((Over.pullback (spMap (algebraMap R W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨R₂, _, _, _, ρ₂, G', _, _, β', X, _, _, _, hfin₂, hpb', ⟨Q⟩⟩ :=
    GlobalTheory.Mum.exists_finExt_tq_closedFibre W ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩ _ hGW
  have hsp : spMap (ρ₂.comp (algebraMap R W)) = spMap ρ₂ ≫ spMap (algebraMap R W) := by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp (algebraMap R W), GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension W R₂ ρ₂ hWd hfin₂,
    ⟨hfin₂.1, hfin₂.2.1.comp hWinj, hfin₂.2.2.comp (RingHom.finite_algebraMap.2 hWfin)⟩, ?_⟩
  intro G₁ _ _ β hβ
  have hGWp := isGrpPullback_pullback G (spMap (algebraMap R W))
  let gam : G₁.left ⟶ ((Over.pullback (spMap (algebraMap R W))).obj G).left :=
    pullback.lift β (G₁.hom ≫ spMap ρ₂) (by rw [hβ.1.w, hsp, Category.assoc])
  have hgam : IsGrpPullback G₁ _ (spMap ρ₂) gam :=
    IsGrpPullback.cancel hGWp (hβ.congr hsp (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨e, he, -⟩ := grpPullback_iso hgam hpb'
  haveI := he
  have hsplit' : SplitClosed G' := ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q⟩⟩
  refine ⟨splitClosed_of_isGrpPullback_id (isGrpPullback_of_iso e) hsplit', ?_⟩
  · let j : FractionRing W →+* FractionRing R₂ :=
      IsLocalization.map (M := nonZeroDivisors W) (T := nonZeroDivisors R₂) (FractionRing R₂) ρ₂
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₂ hfin₂.2.1)
    let i : K' →+* FractionRing R₂ := j.comp (FractionRing.algEquiv W K').symm.toRingHom
    refine H R₂ (ρ₂.comp (algebraMap R W)) i (fun r => ?_) G₁ β hβ
    have h1 := congrArg (fun f => f r) hc
    simp only [RingHom.comp_apply] at h1
    rw [← h1]
    show j ((FractionRing.algEquiv W K').symm (algebraMap W K' (algebraMap R W r))) = _
    rw [AlgEquiv.commutes]
    exact IsLocalization.map_eq _ _

end

end GlobalTheory.Mum
