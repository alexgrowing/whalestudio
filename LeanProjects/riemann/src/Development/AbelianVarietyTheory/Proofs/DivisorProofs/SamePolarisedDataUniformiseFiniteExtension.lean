import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoSectionEvenTranslateSamePolarisedDStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslateStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem samePol_unif_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  have := hR.2
  obtain ⟨a, P, A₂, gen₂, -, hPa, hEv, hgen, hgenL, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_evenTranslate_samePolarisedData R hR D₀ D A G hG U hS
  obtain ⟨D₂, U₂, hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R hR G P hG hEv A₂ gen₂ hgen hgenL
  obtain ⟨R', _, _, _, ρ, D₁, hfin, hloc, ⟨hD₀⟩, hmove⟩ := hcmp D₂ U₂ hLG
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD', A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hfin.1 ρ hfin.2.1 (map_maximalIdeal_le ρ) hG U₂
  obtain ⟨hiso⟩ := hmove D' ⟨hD'⟩
  have hG₁ : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₁, hU₁, -⟩ := (GlobalTheory.T.uniformisation_transfer_isPullDeg_id R' (maximalIdeal R') hfin.1 D₁ D' ⟨hiso⟩ A' _ hG₁).1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  have hpb : IsGrpPullback ((Over.pullback (specOf ρ)).obj G) G (spMap ρ)
      ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    refine (isGrpPullback_pullback G (spMap ρ)).congr ?_ hb.symm
    rfl
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback (Sp R) (Sp R') (spMap ρ) G _ _ hpb
  have hLU : (abelian₂ G U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have h2 : LBIso (abelian₂ G U₂.LG.L) (abelian₂ G U.LG.L) := by
    rw [hLG]
    exact GlobalTheory.T.mumfordBundle_translate_iso_cubical (Sp R) G U.LG U.cubG a P.L.L P.L.isLB hPa
  have h3 : LBIso (abelian₂ G U₂.LG.L) ((abelian₂ G U.LG.L).pull (𝟙 _)) :=
    LBIso.trans (DVR.linComb_isLB _ U₂.LG.isLB _ _) hLU (pull_isLB hLU _) h2
      ⟨GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen hLU⟩
  have h4' := hlam U₂.LG.L U'.LG.L _ (abelian₂ G U.LG.L) (𝟙 _) U₂.LG.isLB U'.LG.isLB hLU
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩ h3
  rw [Category.comp_id] at h4'
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, D₁, _, inferInstance, inferInstance, _, β₂, A', U₁, hfin,
    ⟨hD₀⟩, hpb, hsq, ?_⟩
  rw [hU₁]
  exact h4'

end GlobalTheory.Mum
