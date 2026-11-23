import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormPotentialSumSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_form_potential_sum_smooth : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] (Δ : ι → Y.Dv) (m : ∀ i, (cxSt F).Met Y (I.ε a) (Δ i)) (Q : ι → LocPot (M.X a)) (k : ι → ℤ), (∀ i, IsPot (I.pt a) (m i) (Q i)) → (∀ i, IsPotential (M.A a) (Q i)) → ∑ i, k i • Δ i = 0 → ∃ g : M.X a → ℝ, (M.A a).Smooth g ∧ ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, ∑ i, (k i : ℝ) * leviAt (M.A a) (Q i) j y w = levi (g ∘ ((M.A a).chart j).symm) y w := by
  first | exact @GlobalTheory.LeviRelation.levi_sum_eq_levi_of_relation | exact GlobalTheory.LeviRelation.levi_sum_eq_levi_of_relation | (intros; apply GlobalTheory.LeviRelation.levi_sum_eq_levi_of_relation <;> assumption)
