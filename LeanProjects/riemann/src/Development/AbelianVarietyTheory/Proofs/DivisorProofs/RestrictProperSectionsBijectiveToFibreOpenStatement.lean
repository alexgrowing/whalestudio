import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_surjective_sections_bijective_over_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  first | exact @GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | exact GlobalTheory.restrict_proper_sections_bijective_to_fibre_open | (intros; apply GlobalTheory.restrict_proper_sections_bijective_to_fibre_open <;> assumption)
