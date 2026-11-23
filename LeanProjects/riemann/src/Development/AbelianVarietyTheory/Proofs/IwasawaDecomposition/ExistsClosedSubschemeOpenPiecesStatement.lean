import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedSubschemeOpenPieces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_subscheme_open_pieces : ∀ (P : Scheme.{0}) (J : Type) [Finite J] (T : J → Scheme.{0}) (i : ∀ k, T k ⟶ P) (Ω : P.Opens), (∀ k, IsImmersion (i k)) → (∀ k, IsReduced (T k)) → (∀ k, ∃ U : P.Opens, Set.range (i k) = (⋃ k', Set.range (i k')) ∩ (U : Set P)) → (∃ F : Set P, IsClosed F ∧ ⋃ k, Set.range (i k) = F ∩ (Ω : Set P)) → ∃ (U : Scheme.{0}) (j : U ⟶ Ω.toScheme) (e : ∀ k, T k ⟶ U), IsClosedImmersion j ∧ (∀ k, IsOpenImmersion (e k)) ∧ (∀ k, e k ≫ j ≫ Ω.ι = i k) ∧ ⋃ k, Set.range (e k) = Set.univ := by
  first | exact @GlobalTheory.ReducedUnion.exists_closed_union | exact GlobalTheory.ReducedUnion.exists_closed_union | (intros; apply GlobalTheory.ReducedUnion.exists_closed_union <;> assumption)
