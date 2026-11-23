import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ScalarSectionCompactBlockInvariant

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DomZ (n : ℕ) : Set (M2 n) := {x | x ∈ Dom n ∧ (u1 x).det * (ub1 x).det ∈ Complex.slitPlane}

def KappaC : Prop :=
  ∀ (N : ℕ) (t : ℂ), detD (fun T : Matrix (Fin N) (Fin N) ℂ => (1 + T).det ^ t) = ∏ i ∈ Finset.range N, (t + i)

def CayleyC : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (t : ℂ),
    detD (fun T : Matrix ι ι ℂ => (1 + A * T).det ^ t) = (∏ i ∈ Finset.range (Fintype.card ι), (t + i)) * A.det

def DjZ : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (j : ℕ) (z : ℂ) (x : M2 n), j ≤ n → x ∈ DomZ n →
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1))) =
    (∏ i ∈ Finset.range j, ((i : ℂ) - z)) * (∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z)) *
      fz m e z x * minorOn (blkA j) (wM x) * minorOn (blkB j) (wM x)⁻¹

def FzHol : Prop :=
  ∀ (n m : ℕ) (e : ℤ), IsOpen (DomZ n) ∧ GSet n ⊆ DomZ n ∧
    AnalyticOnNhd ℂ (fun p : ℂ × M2 n => fz m e p.1 p.2) (Set.univ ×ˢ DomZ n)

end PositivityTheory.Rg.Sw.HSt
