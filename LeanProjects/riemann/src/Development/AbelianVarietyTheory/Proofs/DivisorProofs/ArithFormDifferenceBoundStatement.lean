import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithFormDifferenceBound
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_form_difference_bound : ∀ (E : Type 1) [AddCommGroup E] [Module ℝ E] (D : ℕ) (num : Form E D), IsSymm num → ∀ (G : Set E) (o x y h : E) (b : ℝ), x ∈ cone num G → y + h ∈ cone num G → h ∈ cone num G → (∀ N : Fin D → E, (∀ j, N j ∈ G) → |num (Fin.cons (x - y) N)| ≤ b * num (Fin.cons o N)) → (∀ (v : Fin D → E) (j : Fin D), num (Fin.cons o (Function.update v j (x - y))) = 0) → |num (fun _ => x) - num (fun _ => y)| ≤ b * ∑ i : Fin (D + 1), num (Fin.cons o fun j : Fin D => if (j : ℕ) < i then y else y + (2 : ℝ) • h) := by
  first | exact @GlobalTheory.TopPowDiff.abs_top_sub_le | exact GlobalTheory.TopPowDiff.abs_top_sub_le | (intros; apply GlobalTheory.TopPowDiff.abs_top_sub_le <;> assumption)
