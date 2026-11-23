import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.LocalRingCardinality.DataErr

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

open Formalism.BasicNotions Formalism.MainNotions

def minkExp (n p : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1))

def minkNum (n : ℕ) : ℕ := ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime, p ^ minkExp n p

def ratRank (D : D7) : ℕ := 2 * D.R.f * D.R.N D.R.m

def DvdMinkowski (D : D7) : Prop := ∀ u, (D.mem u).C.DGam ∣ minkNum (ratRank D)

def SmallPrimes (D : D7) : Prop := ∀ u (p : ℕ), p.Prime → p ∣ (D.mem u).C.DGam → p ≤ ratRank D + 1

def CoprimeAt (D : D7) : Prop :=
  ∀ u, Nat.Coprime (D.mem u).C.DGam D.host.q ∧ Nat.Coprime (D.mem u).C.DGam D.host.d ∧
    (∀ a : Fin 2, Nat.Coprime (D.mem u).C.DGam (D.host.g a)) ∧
    ∀ u', Nat.Coprime (D.mem u).C.DGam (D.mem u').A.T

def StatementAt (D : D7) : Prop := DvdMinkowski D ∧ SmallPrimes D ∧ CoprimeAt D

def CoprimeF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, CoprimeAt (Fm.D x i)

def StatementF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, StatementAt (Fm.D x i)

example : minkNum 1 = 2 ∧ minkNum 2 = 24 ∧ minkNum 3 = 48 ∧ minkNum 4 = 5760 := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.RationalRankMinkowski

end
