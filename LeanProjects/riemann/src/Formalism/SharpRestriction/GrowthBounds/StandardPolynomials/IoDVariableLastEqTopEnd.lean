import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TgProdPlaces

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

def tgStdE (L : LvDat C0 CE1 CE2 mu X β) : TgPlace X → Bool → Fin (X.m + 1) → ℕ
  | ⟨j, some i⟩, true, c => (β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)
  | ⟨j, some i⟩, false, c => (β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0)
  | ⟨j, none⟩, true, c => if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0
  | ⟨j, none⟩, false, c => Fin.cases 0 (L.γ j) c

def tgStdX (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) : MonH X :=
  Finsupp.equivFunOnFinite.symm fun v => tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm v.1.1) v.1.2 v.2

theorem tgStdX_at (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)) :
    tgStdX h2 L ((tgTop X pl, b), c) = tgStdE L pl b c := by
  unfold tgStdX
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  show tgStdE L ((Equiv.ofBijective _ (tgTop_bij X h2)).symm (tgTop X pl)) b c = _
  rw [Equiv.ofBijective_symm_apply_apply]

variable (O : Type) [CommRing O] [IsDomain O]

theorem tg_ioD_Z (j : Fin (numSeg X.TT)) (l : Fin (X.seg C0 CE1 CE2 j).t) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc l))) =
      MvPolynomial.X ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), true), 0) ^
        (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.castSucc l, false))
  rw [sv_Z, sl_Z] at h
  exact h

theorem ioD_variable_last_eq_top_end (j : Fin (numSeg X.TT)) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
      (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t))) = MvPolynomial.X ((topEnd X j, true), 0) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inr (Fin.last _, false))
  rw [symbol_variable_last, symbol_level_last, pow_one] at h
  exact h

theorem tg_ioD_xi (j : Fin (numSeg X.TT)) (c : Fin X.m) :
    ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c)) =
      MvPolynomial.X ((topEnd X j, false), c.succ) := by
  have h := MvPolynomial.aeval_X (R := KK O) (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : RHH O X) ^
    symLev X.p C0 CE1 CE2 X j v) (Sum.inl (Fin.last (2 * segS X.TT j + 1), c))
  rw [sv_xi, sl_xi, pow_one] at h
  exact h

theorem prod_pow_ite_zero_eq {M : Type} [CommMonoid M] {k : ℕ} (f : Fin (k + 1) → M) (a : ℕ) :
    ∏ c, f c ^ (if c = 0 then a else 0) = f 0 ^ a := by
  rw [Finset.prod_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tg_stdPoly_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) :
    L.stdPoly O j = segMon O X j (tgStdX h2 L) := by
  have hz : ∀ i c, tgStdX h2 L ((topOdd X j i, true), c) = tgStdE L ⟨j, some i⟩ true c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ true c
  have hy : ∀ i c, tgStdX h2 L ((topOdd X j i, false), c) = tgStdE L ⟨j, some i⟩ false c :=
    fun i c => tgStdX_at h2 L ⟨j, some i⟩ false c
  have hx : ∀ c, tgStdX h2 L ((topEnd X j, true), c) = tgStdE L ⟨j, none⟩ true c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ true c
  have hx' : ∀ c, tgStdX h2 L ((topEnd X j, false), c) = tgStdE L ⟨j, none⟩ false c :=
    fun c => tgStdX_at h2 L ⟨j, none⟩ false c
  unfold segMon LvDat.stdPoly
  simp only [hz, hy, hx, hx', tgStdE, map_mul, map_prod, map_pow, ioD_variable_last_eq_top_end, tg_ioD_xi]
  have e1 : ∏ l : Fin (BDk C0 CE1 CE2 mu X β j).T.t,
      (ioD O C0 CE1 CE2 mu X β j (MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
        (Fin.castSucc l)))) ^ (BDk C0 CE1 CE2 mu X β j).T.z l =
      ∏ i : Fin (segS X.TT j), if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1 := by
    rw [← tg_prod_uTop (X.seg C0 CE1 CE2 j) (fun i => ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^
      (X.seg C0 CE1 CE2 j).P X.p i) ^ (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i))]
    refine Finset.prod_congr rfl fun l _ => ?_
    exact congrArg (fun y => y ^ (BDk C0 CE1 CE2 mu X β j).T.z l) (tg_ioD_Z (mu := mu) (β := β) O j l)
  rw [e1]
  have e2 : ∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topEnd X j, true), c) : RHH O X) ^
        (if c = 0 then segAPlus X.TT X.aT j - (β j).oPlus else 0) *
      MvPolynomial.X ((topEnd X j, false), c) ^ (Fin.cases 0 (L.γ j) c : ℕ)) =
      MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) *
        ∏ c : Fin X.m, MvPolynomial.X ((topEnd X j, false), c.succ) ^ L.γ j c := by
    rw [Finset.prod_mul_distrib, prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topEnd X j, true), c) : RHH O X)),
      Fin.prod_univ_succ]
    simp
  rw [e2]
  have e3 : ∀ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
      ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ ((β j).rz i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) else 0)) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ ((β j).ry i c + (if c = 0 then (X.seg C0 CE1 CE2 j).P X.p i *
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) else 0))) =
      (∏ c : Fin (X.m + 1), ((MvPolynomial.X ((topOdd X j i, true), c) : RHH O X) ^ (β j).rz i c *
        MvPolynomial.X ((topOdd X j i, false), c) ^ (β j).ry i c)) *
      ((if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ ((X.seg C0 CE1 CE2 j).P X.p i *
            (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).w i)) *
          MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i * (β j).sg i) else 1) *
       (if (X.seg C0 CE1 CE2 j).sigma ≤ i.val then
        ((MvPolynomial.X ((topOdd X j i, true), 0) : RHH O X) ^ (X.seg C0 CE1 CE2 j).P X.p i) ^
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i - (β j).o i) else 1)) := by
    intro i
    simp only [pow_add]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, true), c) : RHH O X)),
      prod_pow_ite_zero_eq (fun c => (MvPolynomial.X ((topOdd X j i, false), c) : RHH O X)), Finset.prod_mul_distrib]
    by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
    · rw [if_pos hi, if_pos hi, if_pos hi, if_neg (by omega)]
      ring
    · rw [if_neg hi, if_neg hi, if_neg hi, if_pos (by omega), mul_zero, pow_zero, ← pow_mul]
      ring
  rw [Finset.prod_congr rfl fun i _ => e3 i, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold digitMon sTopMon
  show _ * _ * (_ * MvPolynomial.X ((topEnd X j, true), 0) ^ (segAPlus X.TT X.aT j - (β j).oPlus) * _) = _
  ring

theorem tg_std_eq (h2 : 2 ≤ numSeg X.TT) (L : LvDat C0 CE1 CE2 mu X β) (Std : MonH X)
    (h : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) : Std = tgStdX h2 L := by
  have e : (monomial Std (1 : KK O) : RHH O X) = monomial (tgStdX h2 L) 1 := by
    rw [h, tg_mono_split O X h2]
    exact Finset.prod_congr rfl fun j _ => tg_stdPoly_eq O h2 L j
  exact MvPolynomial.monomial_left_injective (one_ne_zero) e

end

end Formalism.MainNotions.ColumnSystems.Pf
