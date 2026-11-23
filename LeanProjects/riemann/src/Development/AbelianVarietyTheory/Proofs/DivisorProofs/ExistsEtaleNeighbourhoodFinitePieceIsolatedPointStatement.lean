import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point : ∀ (U Y : Scheme.{0}) (τ : U ⟶ Y), IsLocallyNoetherian Y → LocallyOfFiniteType τ → IsSeparated τ → ∀ x : U, (∃ O : U.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ Y) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Etale h ∧ PreconnectedSpace T ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ IsFinite (W.ι ≫ pullback.snd τ h) ∧ (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t := by
  first | exact @GlobalTheory.EtaleFinitePiece.main | exact GlobalTheory.EtaleFinitePiece.main | (intros; apply GlobalTheory.EtaleFinitePiece.main <;> assumption)
