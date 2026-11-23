import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultMk
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ThresholdStandardSeventeen

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Exp

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def rPl (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0)) +
    (∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
    ∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)

def zPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))

def nPart (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : MonH X :=
  (∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, false), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0)) +
    ∑ i : Fin (segS X.TT j), ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ)

def stdE (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : MonH X :=
  rPl L j + Finsupp.single ((topEnd X j, true), 0) (segAPlus X.TT X.aT j - (β j).oPlus) + zPart C0 CE1 CE2 X β j +
    nPart C0 CE1 CE2 X β j

theorem stdPoly_eq (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (hsg : ∀ i : Fin (segS X.TT j), ¬ (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma → (β j).sg i = 0) :
    L.stdPoly O j = monomial (stdE L j) 1 := by
  classical
  have hd : digitMon (KK O) C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have hu : (∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l) =
      monomial (∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) 1 := by
    rw [← uTop_sum (X.seg C0 CE1 CE2 j) (fun i => Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))), monomial_sum_one]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ
    rw [ioD_scal, ← pow_mul, X_pow_eq_monomial]
    rfl
  have hx : ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) ^ (BDk C0 CE1 CE2 mu X β j).zPlus =
      monomial (Finsupp.single ((topEnd X j, true), (0 : Fin (X.m + 1))) (segAPlus X.TT X.aT j - (β j).oPlus)) 1 := by
    unfold scalZ
    rw [ioD_scalLast, X_pow_eq_monomial]
    rfl
  have hxi : (∏ c, ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m
      (BDk C0 CE1 CE2 mu X β j).T.t c)) ^ L.γ j c) =
      monomial (∑ c : Fin X.m, Finsupp.single ((topEnd X j, false), c.succ) (L.γ j c)) 1 := by
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [ioD_end β j 1 (by omega) _ (by rfl), X_pow_eq_monomial]
    rfl
  unfold LvDat.stdPoly
  simp only [map_mul, map_prod, map_pow]
  rw [hd, hs, hu, hx, hxi]
  simp only [monomial_mul, one_mul]
  congr 1
  unfold stdE rPl zPart nPart
  have hi : ∀ i : Fin (segS X.TT j),
      (∑ c : Fin (X.m + 1), (Finsupp.single ((topOdd X j i, true), c) ((β j).rz i c) +
        Finsupp.single ((topOdd X j i, false), c) ((β j).ry i c))) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i)
      else 0) +
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
          ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))) =
      Finsupp.single ((topOdd X j i, true), 0) ((β j).rz i 0) +
      (∑ c : Fin X.m, Finsupp.single ((topOdd X j i, false), c.succ) ((β j).ry i c.succ)) +
      Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i))) +
      Finsupp.single ((topOdd X j i, false), 0) ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i + (β j).ry i 0) +
      ∑ c : Fin X.m, Finsupp.single ((topOdd X j i, true), c.succ) ((β j).rz i c.succ) := by
    intro i
    rw [Fin.sum_univ_succ, Finset.sum_add_distrib, Finsupp.single_add]
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · simp only [if_pos h]
      abel
    · simp only [if_neg h, hsg i h, mul_zero, Finsupp.single_zero]
      abel
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (segS X.TT j)))) rfl (fun i _ => hi i)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_add_distrib] at hsum ⊢
  have key : ∀ (a b c d e x y u1 u2 u3 : MonH X), u1 + u2 + u3 = a + b + c + d + e →
      u1 + u2 + (u3 + x + y) = a + b + y + x + c + (d + e) := by
    intro a b c d e x y u1 u2 u3 h
    have : u1 + u2 + (u3 + x + y) = (u1 + u2 + u3) + (x + y) := by abel
    rw [this, h]
    abel
  rw [key _ _ _ _ _ _ _ _ _ _ hsum]

end Exp

end Formalism.MainNotions.ColumnSystems.Pf
