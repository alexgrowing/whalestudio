import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.DensitySumsAndDomination

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem prod_uTop {M : Type} [CommMonoid M] {s : ℕ} (S : SegData s) (f : Fin s → M) :
    ∏ i, f i = (∏ i : Fin s, if (i : ℕ) < S.sigma then f i else 1) * ∏ l : Fin S.t, f (uTop S l) := by
  classical
  have h1 : ∏ l : Fin S.t, f (uTop S l) = ∏ i : Fin s, if S.sigma ≤ i.val then f i else 1 := by
    rw [← Finset.prod_filter]
    refine Finset.prod_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro l _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
    · intro l _ l' _ h
      apply Fin.ext
      have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
      omega
    · intro i hi
      have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
      have := i.2
      exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
        Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < S.sigma
  · rw [if_pos h, if_neg (by omega), mul_one]
  · rw [if_neg h, if_pos (by omega), one_mul]

def mEps (K : Type) [CommRing K] {s r : ℕ} (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    MvPolynomial (Fin (2 * s + 1) × Fin r) K :=
  (∏ i, ∏ c, (X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c)) * ∏ c, X (chU s, c) ^ ax c

section A

variable (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

def ezA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, true), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def eyA (A : MonH X) (i : Fin (segS X.TT j)) (c : Fin X.m) : ℕ :=
  A ((topOdd X j i, false), c.succ) / (X.seg C0 CE1 CE2 j).P X.p i
def axA (A : MonH X) (c : Fin X.m) : ℕ := A ((topEnd X j, true), c.succ)
def z0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, true), 0) / (X.seg C0 CE1 CE2 j).P X.p i
def y0A (A : MonH X) (i : Fin (segS X.TT j)) : ℕ := A ((topOdd X j i, false), 0) / (X.seg C0 CE1 CE2 j).P X.p i

def segmentBlockOfMonomial (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) :
    SegBlock (segS X.TT j) X.m where
  rz := fun i c => A ((topOdd X j i, true), c) % (X.seg C0 CE1 CE2 j).P X.p i
  ry := fun i c => A ((topOdd X j i, false), c) % (X.seg C0 CE1 CE2 j).P X.p i
  o := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else
    jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c
  w := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c else 0
  sg := fun i => if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then y0A C0 CE1 CE2 X j A i else 0
  oPlus := jp + du (chU _) + ∑ c, axA X j A c

theorem ioA_X (v : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :
    ioA (KK O) X.p C0 CE1 CE2 X j (MvPolynomial.X v) =
      MvPolynomial.X (symVar C0 CE1 CE2 X j v) ^ symLev X.p C0 CE1 CE2 X j v := by
  unfold ioA
  rw [aeval_X]

theorem ioA_mEps (ez ey : Fin (segS X.TT j) → Fin X.m → ℕ) (ax : Fin X.m → ℕ) :
    ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (mEps (KK O) ez ey ax)) =
      (∏ i, ∏ c : Fin X.m, ((MvPolynomial.X ((topOdd X j i, true), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ez i c *
        (MvPolynomial.X ((topOdd X j i, false), c.succ) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^ ey i c)) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ ax c := by
  unfold mEps
  simp only [map_mul, map_prod, map_pow, rename_X, chainEmb, ioA_X]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun c _ => ?_
    have a1 := symbol_variable_lower_letter C0 CE1 CE2 X j i c
    have a2 := symbol_level_lower_letter C0 CE1 CE2 X j i c
    have a3 := sv_E C0 CE1 CE2 X j i c
    have a4 := sl_E C0 CE1 CE2 X j i c
    unfold chW chE
    rw [a1, a2, a3, a4]
  · refine Finset.prod_congr rfl fun c _ => ?_
    have a1 := sv_U C0 CE1 CE2 X j c
    have a2 := sl_U C0 CE1 CE2 X j c
    unfold chU
    rw [a1, a2, pow_one]

theorem segMon_eq (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ) (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X)
    (γ : Fin X.m → ℕ)
    (hz0 : ∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
      coarseA X.p (X.seg C0 CE1 CE2 j) (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) i - (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).w i =
        z0A C0 CE1 CE2 X j A i)
    (hy0 : A ((topEnd X j, false), 0) = 0) (hγ : ∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = γ c) :
    segMon O X j A =
      digitMon (KK O) C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
        sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) *
      (ioA (KK O) X.p C0 CE1 CE2 X j (rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t)
          (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A))) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) *
        ioA (KK O) X.p C0 CE1 CE2 X j
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) *
        ioA (KK O) X.p C0 CE1 CE2 X j (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c)) := by
  classical
  set P := fun i => (X.seg C0 CE1 CE2 j).P X.p i with hP
  set Xz : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, true), c) with hXz
  set Xy : Fin (segS X.TT j) → Fin (X.m + 1) → RHH O X := fun i c => MvPolynomial.X ((topOdd X j i, false), c) with hXy

  have i2 : ioA (KK O) X.p C0 CE1 CE2 X j (∏ l : Fin (X.seg C0 CE1 CE2 j).t,
          (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) *
            MvPolynomial.X (scalS (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.castSucc l)) ^
              y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))) =
      ∏ l : Fin (X.seg C0 CE1 CE2 j).t, ((fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i *
        (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) (uTop (X.seg C0 CE1 CE2 j) l)) := by
    simp only [map_prod, map_mul, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun l _ => ?_
    unfold scalZ scalS
    rw [sv_Z, sl_Z, sv_Z, sl_Z]
    rfl
  have i3 : ioA (KK O) X.p C0 CE1 CE2 X j
      (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t (Fin.last _)) ^ A ((topEnd X j, true), 0)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) := by
    rw [map_pow, ioA_X]
    unfold scalZ
    rw [symbol_variable_last, symbol_level_last, pow_one]
    rfl
  have i4 : ioA (KK O) X.p C0 CE1 CE2 X j
      (∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t c) ^ γ c) =
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    simp only [map_prod, map_pow, ioA_X]
    refine Finset.prod_congr rfl fun c _ => ?_
    unfold xiVar
    rw [sv_xi, sl_xi, pow_one]
  rw [ioA_mEps, i2, i3, i4]

  have hS : sTopMon (KK O) X.p C0 CE1 CE2 X j (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A) =
      ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) i else 1 := by
    unfold sTopMon
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos h, if_pos h, hz0 i h]
      have : (segmentBlockOfMonomial C0 CE1 CE2 X j ju jp du A).sg i = y0A C0 CE1 CE2 X j A i := by
        show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
        rw [if_pos h]
      rw [this, pow_mul, pow_mul]
    · rw [if_neg h, if_neg h]
  rw [hS]

  have hodd : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      (Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c)) =
      (∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i))) *
      ((Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i) *
      ∏ c : Fin X.m, ((Xz i c.succ ^ P i) ^ ezA C0 CE1 CE2 X j A i c * (Xy i c.succ ^ P i) ^ eyA C0 CE1 CE2 X j A i c) := by
    intro i
    have e1 : ∀ c : Fin (X.m + 1), Xz i c ^ A ((topOdd X j i, true), c) * Xy i c ^ A ((topOdd X j i, false), c) =
        (Xz i c ^ (A ((topOdd X j i, true), c) % P i) * Xy i c ^ (A ((topOdd X j i, false), c) % P i)) *
        ((Xz i c ^ P i) ^ (A ((topOdd X j i, true), c) / P i) * (Xy i c ^ P i) ^ (A ((topOdd X j i, false), c) / P i)) := by
      intro c
      conv_lhs => rw [← Nat.mod_add_div (A ((topOdd X j i, true), c)) (P i),
        ← Nat.mod_add_div (A ((topOdd X j i, false), c)) (P i)]
      rw [pow_add, pow_add, pow_mul, pow_mul]
      ring
    rw [Finset.prod_congr rfl fun c _ => e1 c, Finset.prod_mul_distrib, mul_assoc]
    congr 1
    rw [Fin.prod_univ_succ]
    rfl
  unfold segMon digitMon
  rw [Finset.prod_congr rfl fun i _ => hodd i, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_uTop (X.seg C0 CE1 CE2 j) (fun i => (Xz i 0 ^ P i) ^ z0A C0 CE1 CE2 X j A i * (Xy i 0 ^ P i) ^ y0A C0 CE1 CE2 X j A i)]
  have hend : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c)) =
      (∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, true), c.succ) ^ axA X j A c) *
      MvPolynomial.X ((topEnd X j, true), 0) ^ A ((topEnd X j, true), 0) *
      ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ γ c := by
    rw [Fin.prod_univ_succ, hy0, pow_zero, mul_one, Finset.prod_mul_distrib]
    simp only [hγ]
    unfold axA
    ring
  rw [hend]
  show (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _ * _ =
    (∏ i, ∏ c : Fin (X.m + 1), (Xz i c ^ (A ((topOdd X j i, true), c) % P i) *
      Xy i c ^ (A ((topOdd X j i, false), c) % P i))) * _ * _
  ring

end A

end Formalism.MainNotions.ColumnSystems.Pf
