import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGlueCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_glue_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {I : Type} {R : I → Type} [∀ i, CommRing (R i)] {ω : ∀ i, R i →+* c.F} (Z : Model Xo c β) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X) (φ : InvFun (𝓞 E)) (DZ : EffCartierData Z.X) (BD : ∀ i, EffCartierData (C i).X), (∀ i, IsOpenImmersion (u i)) → (∀ i, (C i).j ≫ u i = Z.j) → (∀ i, Nonempty (SABMap (C i).t Z.t (u i))) → (∀ x : Z.X, ∃ i, x ∈ Set.range (u i)) → (∀ i, DZ.idealSheaf.comap (u i) = (BD i).idealSheaf) → (∀ i, IsPhiDiv φ (C i) (BD i)) → IsPhiDiv φ Z DZ := by
  first | exact @GlobalTheory.TorRef.isPhiDiv_of_openCover | exact GlobalTheory.TorRef.isPhiDiv_of_openCover | (intros; apply GlobalTheory.TorRef.isPhiDiv_of_openCover <;> assumption)
