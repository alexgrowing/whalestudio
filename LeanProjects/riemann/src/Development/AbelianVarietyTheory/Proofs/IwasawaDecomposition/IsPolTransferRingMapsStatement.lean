import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolTransferRingMaps
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
theorem _root_.GlobalTheory.T.isPol_transfer_ring_maps : PolMapSt → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Z : Model Xo c β) (Z' : Model Xo c β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X) (φ : InvFun (𝓞 E))
    (m : ℕ) (b : O →+* O') (b' : O' →+* O), Models.IsDedFrac β → Models.IsDedFrac β' → Algebra.FiniteType ℤ O →
    Algebra.FiniteType ℤ O' → IsTwInv H φ → β'.comp b = β → β.comp b' = β' → IsPol φ m Z BD → IsPol φ m Z' BD' →
    ∃ θ : Z'.X ≅ Z.X, θ.hom ≫ Z.s = Z'.s ≫ spMap b ∧ Z'.j ≫ θ.hom = Z.j ∧ BD'.idealSheaf = BD.idealSheaf.comap θ.hom := by
  first | exact @GlobalTheory.PolModelIso.exists_iso_of_isPol | exact GlobalTheory.PolModelIso.exists_iso_of_isPol | (intros; apply GlobalTheory.PolModelIso.exists_iso_of_isPol <;> assumption)
