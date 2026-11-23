import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem movePositionToLast : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (e : ℕ) (L : Fin (e + 1) → HermLine ι) (i : Fin (e + 1)), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → I P (e + 1) L = I P (e + 1) (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i)) := by
  intro K _ ι _ I hI P e L i hP hL
  let σ : Equiv.Perm (Fin (e + 1)) := (finSuccEquivLast (n := e)).trans (finSuccEquiv' i).symm
  have h : (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i) : Fin (e + 1) → HermLine ι) = L ∘ σ := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [σ]
    · simp [σ]
  rw [h]
  exact (hI.1 P (e + 1) L σ hP hL).symm

end GlobalTheory.CompanionTheory.Ar.Cmp
