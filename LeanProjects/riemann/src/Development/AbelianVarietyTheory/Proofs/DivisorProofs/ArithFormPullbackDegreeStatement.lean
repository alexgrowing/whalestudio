import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithFormPullbackDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_form_pullback_degree : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q), π (genericPoint X') = genericPoint X → π.residueDegree (genericPoint X') ≠ 0 → ∀ (num : Form (Cl p) D) (num' : Form (Cl q) D), IsArForm D num → IsArForm D num' → (∀ v : Fin (D + 1) → Cl p, num' (fun j => pullCl π hπ (v j)) = (π.residueDegree (genericPoint X') : ℝ) * num v) ∧ pullCl π hπ (cl (oneB p)) - cl (oneB q) ∈ rad num' := by
  first | exact @GlobalTheory.VertForm.PullForm.arForm_pull | exact GlobalTheory.VertForm.PullForm.arForm_pull | (intros; apply GlobalTheory.VertForm.PullForm.arForm_pull <;> assumption)
