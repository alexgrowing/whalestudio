import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricTranslates_multiplication_pullback_description : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N : ℕ), Odd N → ∀ (s : SecN Xo x 1), (∀ (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F ↔ ∃ F₀ F₁ : SecN Xo x (N ^ 2), Pulls Xo (N : 𝓞 E) s F₀ ∧ Moves Xo x₁ F₀ F₁ ∧ Moves Xo x₂ F₁ (sqN Xo N F))) ∧ ∀ (ok : (ptO Xo x ⟶ Xo.univ.t.G) → Prop) (t : (ptO Xo x ⟶ Xo.univ.t.G)) (F), t ^ N = 1 → IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F → ∃ t' : (ptO Xo x ⟶ Xo.univ.t.G), t' ^ N = t ∧ ok t' ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N s 1 t' F := by
  first | exact @GlobalTheory.PlaceInt.uu_through_moves | exact GlobalTheory.PlaceInt.uu_through_moves | (intros; apply GlobalTheory.PlaceInt.uu_through_moves <;> assumption)
