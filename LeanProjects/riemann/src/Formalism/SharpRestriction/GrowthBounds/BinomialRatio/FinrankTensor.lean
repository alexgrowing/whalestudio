import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem prodUp (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have h := Nat.add_one_mul_choose_eq (A + m) m
    have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
      rw [h]
    push_cast at h'
    have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
    rw [show A + (m + 1) = A + m + 1 from rfl]
    field_simp
    linarith

theorem prodDown (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodUp, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h : ((Fin.revPerm j : Fin m) : ℕ) + ((j : ℕ) + 1) = m := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    omega
  have h' : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) + (((j : ℕ) : ℚ) + 1) = (m : ℚ) := by exact_mod_cast h
  rw [← h']
  congr 1 <;> ring

def wprod (n : ℕ) (nu : Fin n → ℕ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

theorem ratio_one {n : ℕ} {i j : Fin n} (h : i < j) (x : ℚ) :
    (x - x + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) = 1 := by
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast h
  have h2 : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by linarith
  rw [sub_self, zero_add]
  exact div_self h2

theorem wprod_vec (m d : ℕ) : wprod (m + 1) (fun i => if i = 0 then d else 0) = ((d + m).choose m : ℚ) := by
  unfold wprod
  rw [Fin.prod_univ_succ]
  have h2 : ∏ i : Fin m, ∏ j : Fin (m + 1),
      (if i.succ < j then
        ((((if i.succ = 0 then d else 0 : ℕ)) : ℚ) - (((if j = 0 then d else 0 : ℕ)) : ℚ) + (j : ℚ) - (i.succ : ℚ)) /
          ((j : ℚ) - (i.succ : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro i _
    apply Finset.prod_eq_one; intro j _
    split_ifs with h h1 h3 h3
    · exact absurd h1 (Fin.succ_ne_zero i)
    · exact absurd h1 (Fin.succ_ne_zero i)
    · subst h3; exact absurd h (Fin.not_lt_zero _)
    · exact ratio_one h _
    · rfl
  rw [h2, mul_one, Fin.prod_univ_succ, ← prodUp]
  simp only [lt_self_iff_false, if_false, one_mul, if_true]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [if_pos (Fin.succ_pos j), if_neg (Fin.succ_ne_zero j)]
  simp only [Fin.val_succ, Fin.val_zero, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

theorem wprod_cov (m d : ℕ) :
    wprod (m + 1) (fun i => if i = Fin.last m then 0 else d) = ((d + m).choose m : ℚ) := by
  unfold wprod
  rw [Fin.prod_univ_castSucc]
  have h2 : ∏ j : Fin (m + 1),
      (if Fin.last m < j then
        ((((if Fin.last m = Fin.last m then 0 else d : ℕ)) : ℚ) - (((if j = Fin.last m then 0 else d : ℕ)) : ℚ) +
          (j : ℚ) - ((Fin.last m : Fin (m + 1)) : ℚ)) / ((j : ℚ) - ((Fin.last m : Fin (m + 1)) : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro j _
    rw [if_neg (not_lt.mpr (Fin.le_last j))]
  rw [h2, mul_one, ← prodDown]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  have h3 : ∏ j : Fin m,
      (if i.castSucc < j.castSucc then
        ((((if i.castSucc = Fin.last m then 0 else d : ℕ)) : ℚ) - (((if j.castSucc = Fin.last m then 0 else d : ℕ)) : ℚ) +
          (j.castSucc : ℚ) - (i.castSucc : ℚ)) / ((j.castSucc : ℚ) - (i.castSucc : ℚ)) else 1) = 1 := by
    apply Finset.prod_eq_one; intro j _
    rw [if_neg (Fin.castSucc_lt_last i).ne, if_neg (Fin.castSucc_lt_last j).ne]
    by_cases h : i.castSucc < j.castSucc
    · rw [if_pos h]
      exact ratio_one h _
    · rw [if_neg h]
  rw [h3, one_mul, if_pos (Fin.castSucc_lt_last i)]
  simp only [if_neg (Fin.castSucc_lt_last i).ne, if_true, Fin.val_castSucc, Fin.val_last, Nat.cast_zero, sub_zero]

theorem last_ne_zero {m : ℕ} (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem finrank_letter {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (K : Type) [Field K] [CharZero K] (m d : ℕ) (hm : 1 ≤ m)
    (vec : Bool) :
    Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (letterWt m d vec))) = sd m d := by
  have hq : (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (letterWt m d vec))) : ℚ) = (sd m d : ℚ) := by
    cases vec with
    | true =>
      have hnu : nuOf (letterWt m d true) = fun i => if i = 0 then d else 0 := by
        funext i
        simp only [nuOf, letterWt, if_true, if_neg (last_ne_zero hm), sub_zero]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt m d true)) := by
        rw [hnu]
        intro i j hij
        simp only
        split_ifs with h1 h2 <;> first | omega | skip
        exact absurd (Fin.le_zero_iff.1 (h1 ▸ hij)) h2
      rw [h3 K _ _ hanti, hnu]
      exact wprod_vec m d
    | false =>
      have hnu : nuOf (letterWt m d false) = fun i => if i = Fin.last m then 0 else d := by
        funext i
        simp only [nuOf, letterWt, Bool.false_eq_true, if_false, if_true]
        split_ifs <;> simp
      have hanti : Antitone (nuOf (letterWt m d false)) := by
        rw [hnu]
        intro i j hij
        simp only
        by_cases hj : j = Fin.last m
        · rw [if_pos hj]; exact Nat.zero_le _
        · have hi : i ≠ Fin.last m := fun h => hj (le_antisymm (Fin.le_last _) (h ▸ hij))
          rw [if_neg hj, if_neg hi]
      rw [h3 K _ _ hanti, hnu]
      exact wprod_cov m d
  exact_mod_cast hq

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  classical
  have hb := fun s : S => Formalism.GradedWeylDivisibility.sSBasis Kf k n (ν s)
  choose b hb1 _ using hb
  have : IsFractionRing Kf Kf :=
    IsLocalization.of_le_isUnit (fun x hx => IsUnit.mk0 x (nonZeroDivisors.ne_zero hx))
  obtain ⟨hli, hsp⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => ↥(Formalism.GradedWeylDivisibility.ssIdx k n (ν s)))
    (fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) b (fun s => (hb1 s).1) (fun s => (hb1 s).2.1)
  have : ∀ s : S, Fintype ↥(Formalism.GradedWeylDivisibility.ssIdx k n (ν s)) := fun s => (Formalism.GradedWeylDivisibility.sSIdxFinite k n (ν s)).fintype
  rw [← hsp, finrank_span_eq_card hli, Fintype.card_pi]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← (hb1 s).2.1, finrank_span_eq_card (hb1 s).1]

theorem dimHH_of {D : Formalism.BasicNotions.D7} (h3 : adm3 D) : DimHHAt := by
  intro Kf _ _ n' m TT aT bT hm
  classical
  unfold dimHH VHH
  rw [finrank_tensor Kf (TT × Bool) (m + 1) (m + 1) (fun x => nuOf (hhWt m TT aT bT x))]
  have h1 : ∀ x : TT × Bool,
      Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (hhWt m TT aT bT x))) =
        sd m (hhDeg aT bT x.1.val x.2) := fun x => finrank_letter h3 Kf m _ hm x.2
  rw [Finset.prod_congr rfl fun x _ => h1 x, Fintype.prod_prod_type]
  rw [← Finset.prod_coe_sort TT fun s => sd m (aT s) * sd m (bT s)]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fintype.prod_bool]
  unfold hhDeg
  by_cases he : Even s.val.val
  · simp [he]
  · simp [he, mul_comm]

theorem charZeroAt : CharZeroAt := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS
  have hw : Irreducible w := hS.2.1
  have hpw : w ^ 2 = (p : O) := hS.1.w_sq
  have hp0 : (p : O) ≠ 0 := by rw [← hpw]; exact pow_ne_zero _ hw.ne_zero
  have hpu : ¬ IsUnit (p : O) := by
    rw [← hpw]
    intro h
    exact hw.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [pow_two] at h))
  have hO : CharZero O := by
    obtain ⟨c, hc⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O c with h | h
    · exfalso
      have hc0 : (c : O) = 0 := CharP.cast_eq_zero O c
      by_cases hcp : c = p
      · exact hp0 (hcp ▸ hc0)
      · have hcop : Nat.Coprime c p := (Nat.coprime_primes h hS.1.prime).2 hcp
        obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
        have h1 : ((a * c + b * p : ℤ) : O) = 1 := by rw [hab]; simp
        push_cast at h1
        rw [hc0, mul_zero, zero_add] at h1
        exact hpu (IsUnit.of_mul_eq_one_right _ h1)
    · subst h
      exact CharP.charP_to_charZero O
  have hfr : IsFractionRing O Kf := hS.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O Kf)

end Formalism.MainNotions.ColumnSystems.Pf
