import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_defect_formula : RatRStatement → ResBridgeStatement → GoodProjExistsStatement → AvoidStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A B : HermLine ι) (f g : MRing ι) (w : ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B → IsLineIso P A.a B.a f g → IsDefectOn P (mcPts P) f g A B w → I P (e + 1) (Fin.snoc L A) - I P (e + 1) (Fin.snoc L B) = -mInt R.A (fun j => potOf R (L j)) (fun x => w (R.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | exact GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.inter_sub_eq_neg_mInt <;> assumption)
