import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolLocalizationAway
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPol_localization_away : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {R : Type} [CommRing R] {ω : R →+* c.F} (C : Model Xo c ω) (BD : EffCartierData C.X) (φ : InvFun (𝓞 E))
    (m : ℕ) (x : R) (ω' : Localization.Away x →+* c.F), Models.IsDedFrac ω → Models.IsDedFrac ω' →
    ω'.comp (algebraMap R (Localization.Away x)) = ω → IsPol φ m C BD →
    ∃ (C' : Model Xo c ω') (BD' : EffCartierData C'.X) (v : C'.X ⟶ C.X),
      IsPullback v C'.s C.s (spMap (algebraMap R (Localization.Away x))) ∧ C'.j ≫ v = C.j ∧ IsPol φ m C' BD' ∧
        BD'.idealSheaf = BD.idealSheaf.comap v := by
  first | exact @GlobalTheory.PolRestr.exists_isPol_away | exact GlobalTheory.PolRestr.exists_isPol_away | (intros; apply GlobalTheory.PolRestr.exists_isPol_away <;> assumption)
