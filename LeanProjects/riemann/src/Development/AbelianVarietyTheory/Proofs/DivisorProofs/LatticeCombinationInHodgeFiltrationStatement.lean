import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCombinationInHodgeFiltration
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_combination_in_hodge_filtration : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (P : u.Λ →+ HdR A), LieExact A → (∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) →
    ∀ c : u.Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ Fil A ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0 := by
  first | exact @GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff | exact GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff | (intros; apply GlobalTheory.HodgeUnif.sum_smul_mem_fil_iff <;> assumption)
