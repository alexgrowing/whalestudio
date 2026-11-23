import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeSplitIndexPrimeTo
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_split_index_prime_to : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (q : ℕ), q.Prime → ¬ q ∣ 2 * H.d * (discr E).natAbs → ∃ (Lp Lm : Submodule (𝓞 E) D.La) (N : ℕ), ¬ q ∣ N ∧ (∀ v : D.La, N • v ∈ Lp ⊔ Lm) ∧ (∀ a ∈ Lp, ∀ b ∈ Lm, D.EF a b = 0) ∧ (∀ a ∈ Lp, 0 ≤ H.rt0.im * D.EF (H.w0 • a) a) ∧ ∀ a ∈ Lm, H.rt0.im * D.EF (H.w0 • a) a ≤ 0 := by
  first | exact @GlobalTheory.LatSplitPrime.exists_split_prime_to | exact GlobalTheory.LatSplitPrime.exists_split_prime_to | (intros; apply GlobalTheory.LatSplitPrime.exists_split_prime_to <;> assumption)
