import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_class_form_properties : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num → (∀ L M : HermLB p, cl (L.tens M) - (cl L + cl M) ∈ rad num) ∧ (∀ L : HermLB p, cl L.dual + cl L ∈ rad num) ∧ (∀ L M : HermLB p, L.Isometric M → cl L - cl M ∈ rad num) ∧ ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ), cl (ArInt.comb L n) - ∑ i, (n i : ℝ) • cl (L i) ∈ rad num := by
  first | exact @GlobalTheory.VertForm.arForm_rad_rules | exact GlobalTheory.VertForm.arForm_rad_rules | (intros; apply GlobalTheory.VertForm.arForm_rad_rules <;> assumption)
