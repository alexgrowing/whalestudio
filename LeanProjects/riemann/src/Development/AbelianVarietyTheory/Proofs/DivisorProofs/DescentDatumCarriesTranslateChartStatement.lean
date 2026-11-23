import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumCarriesTranslateChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_carries_translateChart : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (N : Near π G') (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, N.Pt (𝟙 S) (π ≫ a i) (x i).left) → ∀ φ, N.Datum φ → ∀ (j : Option (Fin n)) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback N.U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback G'.hom (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ N.chart x j → z ≫ pullback.snd _ _ = s → z ≫ φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) = y₂ ≫ N.chart x j := by
  first | exact @GlobalTheory.Mum.Near.datum_chart | exact GlobalTheory.Mum.Near.datum_chart | (intros; apply GlobalTheory.Mum.Near.datum_chart <;> assumption)
