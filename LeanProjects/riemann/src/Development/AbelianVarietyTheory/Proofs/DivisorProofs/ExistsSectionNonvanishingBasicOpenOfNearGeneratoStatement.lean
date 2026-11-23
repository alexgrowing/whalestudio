import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGenerato
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_basicOpen_of_nearGenerator : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X → QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens), (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen → ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  first | exact @GlobalTheory.GenNearExtend.exists_sec_of_gen_near | exact GlobalTheory.GenNearExtend.exists_sec_of_gen_near | (intros; apply GlobalTheory.GenNearExtend.exists_sec_of_gen_near <;> assumption)
