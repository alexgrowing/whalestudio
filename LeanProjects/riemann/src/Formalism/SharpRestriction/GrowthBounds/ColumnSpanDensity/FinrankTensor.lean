import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
import Formalism.PolynomialDimension.MultinomialDepth.WeylDimPosOfAntitone
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

private theorem choose_add_succ_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + (m + 1)).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * ((A : ℚ) + m + 1) / ((m : ℚ) + 1) := by
  have h : (A + m + 1) * (A + m).choose m = (A + m + 1).choose (m + 1) * (m + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq (A + m) m
    | exact Nat.succ_mul_choose_eq (A + m) m
  rw [eq_div_iff (by positivity), show A + (m + 1) = A + m + 1 by omega]
  have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination -h'

private theorem choose_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + m).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * (A : ℚ) / ((m : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (A + m) m
  rw [Nat.add_sub_cancel] at h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast h

theorem prodA (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, choose_add_succ_succ_eq_choose_mul_div]
    ring

theorem prodB (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodA m B, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hr : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) = (m : ℚ) - ((j : ℕ) : ℚ) - 1 := by
    rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hr]
  congr 1 <;> ring

theorem weylDim_const (m : ℕ) (d : ℤ) : weylDim m (fun _ => d) = 1 := by
  unfold weylDim
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℕ) < (j : ℕ) := h
    have hq : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
    simp only [sub_self, Int.cast_zero, zero_add]
    exact div_self (sub_pos.mpr hq).ne'
  · rfl

private theorem weylDim_cons_eq_prod_mul (n : ℕ) (a : ℤ) (lam : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons a lam) =
      (∏ j : Fin n, (((a - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n lam := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [lt_self_iff_false, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [if_pos (Fin.succ_pos j)]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    push_cast
    congr 1 <;> ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.not_lt_zero, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.cons_succ, Fin.val_succ, Fin.succ_lt_succ_iff]
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

private theorem weylDim_snoc_eq_mul_prod (n : ℕ) (lam : Fin n → ℤ) (b : ℤ) :
    weylDim (n + 1) (Fin.snoc lam b) =
      weylDim n lam * ∏ i : Fin n, (((lam i - b : ℤ) : ℚ) + (n : ℚ) - ((i : ℕ) : ℚ)) / ((n : ℚ) - ((i : ℕ) : ℚ)) := by
  unfold weylDim
  have h1 : ∀ g : Fin (n + 1) → ℚ, (∏ j : Fin (n + 1), if Fin.last n < j then g j else 1) = 1 :=
    fun g => Finset.prod_eq_one fun j _ => if_neg (not_lt.mpr (Fin.le_last j))
  rw [Fin.prod_univ_castSucc, h1, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc, Fin.castSucc_lt_castSucc_iff]
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]

theorem weylDim_hwt_eq (m A B : ℕ) : weylDim (m + 2) (hwt m A B) = (dimHar (m + 1) A B : ℚ) := by
  unfold hwt
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_zero, zero_sub, neg_neg, sub_neg_eq_add, zero_add]
  rw [prodA m A, prodB m B]
  unfold dimHar dimPol
  have hle : (if A = 0 ∨ B = 0 then 0 else (A - 1 + (m + 1)).choose (m + 1) * (B - 1 + (m + 1)).choose (m + 1)) ≤
      (A + (m + 1)).choose (m + 1) * (B + (m + 1)).choose (m + 1) := by
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
  rw [Nat.cast_sub hle, Nat.cast_mul, choose_add_succ_succ_eq_choose_mul_div A m, choose_add_succ_succ_eq_choose_mul_div B m]
  split_ifs with h
  · rcases h with rfl | rfl <;> push_cast <;> field_simp <;> ring
  · push_neg at h
    rw [Nat.cast_mul, show A - 1 + (m + 1) = A + m by omega, show B - 1 + (m + 1) = B + m by omega,
      choose_succ_eq_choose_mul_div A m, choose_succ_eq_choose_mul_div B m]
    field_simp
    ring

theorem weylDim_vec (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  have hz : (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0 : Fin (m + 1) → ℤ) = fun _ => 0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [hz, weylDim_cons_eq_prod_mul, weylDim_const, mul_one]
  push_cast
  try simp only [sub_zero]
  rw [prodA (m + 1) d]

theorem weylDim_cov (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (d : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_self, zero_add, sub_zero]
  have h1 : (∏ j : Fin m, (((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = 1 :=
    Finset.prod_eq_one fun j _ => div_self (by positivity)
  rw [prodB m d, h1, one_mul, choose_add_succ_succ_eq_choose_mul_div d m]
  ring

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  classical
  haveI : IsFractionRing Kf Kf := by
    first
    | infer_instance
    | exact IsLocalization.atUnits Kf (nonZeroDivisors Kf)
        (fun x hx => (IsUnit.mem_submonoid_iff _).mpr (Ne.isUnit (nonZeroDivisors.ne_zero hx)))
  let M : S → Submodule Kf (MvPolynomial (Fin k × Fin n) Kf) := fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)
  let B : ∀ s, Module.Basis (Module.Basis.ofVectorSpaceIndex Kf (M s)) Kf (M s) :=
    fun s => Module.Basis.ofVectorSpace Kf (M s)
  let b : ∀ s, Module.Basis.ofVectorSpaceIndex Kf (M s) → MvPolynomial (Fin k × Fin n) Kf :=
    fun s i => ((B s i : M s) : MvPolynomial (Fin k × Fin n) Kf)
  have hli : ∀ s, LinearIndependent Kf (b s) := fun s =>
    (B s).linearIndependent.map' (M s).subtype (Submodule.ker_subtype _)
  have hsp : ∀ s, Submodule.span Kf (Set.range (b s)) = M s := by
    intro s
    have h1 : Set.range (b s) = (M s).subtype '' Set.range (B s) := by
      rw [← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, (B s).span_eq, Submodule.map_subtype_top]
  obtain ⟨hT, hTs⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => Module.Basis.ofVectorSpaceIndex Kf (M s)) M b hli hsp
  show Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf M) = _
  rw [← hTs, Module.finrank_eq_nat_card_basis (Module.Basis.span hT), Nat.card_pi]
  exact Finset.prod_congr rfl fun s _ => (Module.finrank_eq_nat_card_basis (B s)).symm

theorem RS.charZeroO {p n' : ℕ} (R : RS p n') : CharZero R.O := by
  obtain ⟨c, hc⟩ := CharP.exists R.O
  rcases CharP.char_is_prime_or_zero R.O c with h | h
  · exfalso
    have hc0 : (c : R.O) = 0 := CharP.cast_eq_zero R.O c
    by_cases hcp : c = p
    · exact R.p_ne (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h R.std.1.prime).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : R.O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact R.p_not_unit (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero R.O

theorem RS.charZero {p n' : ℕ} (R : RS p n') : CharZero R.Kf := by
  have := R.charZeroO
  have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective R.O R.Kf)

end Formalism.MainNotions.flipOneThree.Pf

end
