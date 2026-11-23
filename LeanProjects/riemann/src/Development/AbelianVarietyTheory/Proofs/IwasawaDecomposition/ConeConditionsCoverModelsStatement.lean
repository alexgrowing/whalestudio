import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_conditions_cover_models : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsChartOf Z (C i) (a i) (b i) (u i)) → (∀ i, HasCones Cn (C i)) → HasCones Cn Z := by
  first | exact @GlobalTheory.TorRef.hasCones_of_charts | exact GlobalTheory.TorRef.hasCones_of_charts | (intros; apply GlobalTheory.TorRef.hasCones_of_charts <;> assumption)
