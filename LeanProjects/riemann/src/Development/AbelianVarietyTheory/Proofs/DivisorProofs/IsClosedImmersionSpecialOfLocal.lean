import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionOfBaseChangeFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtensionStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj
open MonObj
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibre

open GlobalTheory.SplitTorus (torusMap bcIso)

theorem isClosedImmersion_special_of_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Type) [Field K] [Algebra R K]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G], IsSemiAbelian G →
    ∀ (r : ℕ) (u : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r ⟶ G), IsMonHom u →
    Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u) →
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left := by
  intro R _ _ _ K _ _ G _ hG r u hu hmono
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  refine GlobalTheory.T.closedImmersion_of_baseChange_field_ext R k Ω (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.torus R r) G u ?_
  let p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  obtain ⟨E⟩ := hG.fibres Ω p
  let v := (bcIso p (Fin r → ℤ)).hom ≫ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u
  have hv : IsClosedImmersion v.left := by
    refine GlobalTheory.T.isClosedImmersion_splitTorus_into_torusExtension Ω _ E r v inferInstance fun q hq φ hφ h => hφ ?_
    have hsep : IsSeparated G.hom := hG.separated
    have e1 : torusMap _ φ ≫ (bcIso p (Fin r → ℤ)).hom =
        (bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ) :=
      (GlobalTheory.SplitTorus.comm_bcMap_iff p _ _).1 (GlobalTheory.SplitTorus.torusMap_bcMap p φ)

    have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map (torusMap _ φ ≫ u) =
        (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map 1 := by
      rw [Functor.map_comp, Functor.map_one, ← cancel_epi (bcIso p (ZMod q)).hom, MonObj.comp_one,
        ← Category.assoc]
      change ((bcIso p (ZMod q)).hom ≫ (Over.pullback p).map (torusMap _ φ)) ≫ _ = _
      rw [← e1, Category.assoc]
      exact h

    have hk := GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension R k Ω _ _ _ _ hΩ
    have hf : torusMap _ φ ≫ u = 1 :=
      GlobalTheory.T.splitTorus_hom_ext_of_eq_mod_maximalIdeal_pow R (ZMod q) G hsep _ _ (GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one R (ZMod q) G _ inferInstance hk)

    let pK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R K))
    have hK' : (Over.pullback pK).map (torusMap _ φ) = (Over.pullback pK).map (torusMap _ 0) := by
      rw [← cancel_mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R K).map u)]
      change (Over.pullback pK).map (torusMap _ φ) ≫ (Over.pullback pK).map u =
        (Over.pullback pK).map (torusMap _ 0) ≫ (Over.pullback pK).map u
      rw [← Functor.map_comp, ← Functor.map_comp, hf, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]
    rw [GlobalTheory.SplitTorus.pullback_map_torusMap, GlobalTheory.SplitTorus.pullback_map_torusMap,
      cancel_epi, cancel_mono] at hK'
    exact GlobalTheory.SplitTorus.torusMap_injective hK'
  have : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map u = (bcIso p (Fin r → ℤ)).inv ≫ v := by
    simp [v]
  rw [this, Over.comp_left]
  haveI : IsIso (bcIso p (Fin r → ℤ)).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (bcIso p (Fin r → ℤ)).inv))
  exact IsClosedImmersion.comp _ _

end GlobalTheory.TorusFibre
