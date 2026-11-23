import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactAbs
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Kummer

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees MvPolynomial

theorem rat_int {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [CharZero K] [Algebra O K] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) (x : ℚ) (c : ℕ) (hx : PadicGe p x c) :
    ∃ y : O, (x : K) = (p : K) ^ c * algebraMap O K y := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  rcases hx with hx | hv
  · exact absurd hx hx0
  haveI : Fact p.Prime := ⟨hp⟩
  have hv' : (c : ℤ) ≤ padicValRat p x := by exact_mod_cast hv
  simp only [padicValRat] at hv'
  have hden : ¬ p ∣ x.den := by
    intro hd
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have h1 : p ∣ x.num.natAbs := Int.ofNat_dvd_left.mp hn
      have h2 := Nat.dvd_gcd h1 hd
      rw [x.reduced.gcd_eq_one] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have h0 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    rw [h0] at hv'
    omega
  have hpv0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  rw [hpv0] at hv'
  have hdvd : (p : ℤ) ^ c ∣ x.num := by
    have := (padicValInt_dvd_iff (p := p) c x.num).mpr (Or.inr (by omega))
    exact_mod_cast this
  obtain ⟨n, hn⟩ := hdvd
  have hcop : Nat.Coprime p x.den := (Nat.Prime.coprime_iff_not_dvd hp).mpr hden
  have hb := Nat.gcd_eq_gcd_ab p x.den
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (p : O) * (Nat.gcdA p x.den : O) + (x.den : O) * (Nat.gcdB p x.den : O) = 1 := by
    have := congrArg (Int.cast : ℤ → O) hb
    push_cast at this
    exact this.symm
  have hdu : IsUnit (x.den : O) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hb' with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) hpO
    · exact isUnit_of_mul_isUnit_left h
  have hinv : algebraMap O K (↑hdu.unit⁻¹ : O) * (x.den : K) = 1 := by
    rw [← map_natCast (algebraMap O K), ← map_mul, IsUnit.val_inv_mul, map_one]
  have hainv : algebraMap O K (↑hdu.unit⁻¹ : O) = (x.den : K)⁻¹ := eq_inv_of_mul_eq_one_left hinv
  refine ⟨(n : O) * ↑hdu.unit⁻¹, ?_⟩
  rw [map_mul, map_intCast, hainv, Rat.cast_def, hn]
  push_cast
  ring

def Rblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  open Classical in
  ∏ x ∈ Finset.univ \ (Finset.univ.image (symVar C0 CE1 CE2 X j)), (baseExp C0 CE1 CE2 X j b x).factorial

theorem expFact_ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    expFact (ioExp C0 CE1 CE2 X j b μ) = Rblk C0 CE1 CE2 X j b *
      ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
        symLev X.p C0 CE1 CE2 X j v * μ v).factorial := by
  classical
  have hinj := symVar_inj C0 CE1 CE2 X j
  have hsumv : ∀ x, (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) x =
      ∑ v ∈ μ.support, if symVar C0 CE1 CE2 X j v = x then symLev X.p C0 CE1 CE2 X j v * μ v else 0 := by
    intro x
    rw [Finsupp.sum_apply]
    exact Finset.sum_congr rfl fun v _ => Finsupp.single_apply
  have hout : ∀ x ∉ Finset.univ.image (symVar C0 CE1 CE2 X j),
      ioExp C0 CE1 CE2 X j b μ x = baseExp C0 CE1 CE2 X j b x := by
    intro x hx
    rw [ioExp, Finsupp.add_apply, hsumv, Finset.sum_eq_zero, add_zero]
    intro v _
    rw [if_neg]
    intro h
    exact hx (Finset.mem_image.2 ⟨v, Finset.mem_univ _, h⟩)
  have hin : ∀ v, ioExp C0 CE1 CE2 X j b μ (symVar C0 CE1 CE2 X j v) =
      baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) + symLev X.p C0 CE1 CE2 X j v * μ v := by
    intro v
    rw [ioExp, Finsupp.add_apply, hsumv]
    congr 1
    rw [Finset.sum_eq_single v]
    · rw [if_pos rfl]
    · intro v' _ hne
      rw [if_neg]
      exact fun h => hne (hinj h)
    · intro hv
      have h0 : μ v = 0 := by simpa using hv
      rw [if_pos rfl, h0, mul_zero]
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.image (symVar C0 CE1 CE2 X j)))]
  rw [Finset.prod_image (fun a _ c _ h => hinj h)]
  congr 1
  · unfold Rblk
    exact Finset.prod_congr rfl fun x hx => by rw [hout x (Finset.mem_sdiff.1 hx).2]
  · exact Finset.prod_congr rfl fun v _ => by rw [hin v]

theorem baseExp_odd (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (i0 : Fin (segS X.TT j)) (β0 : Bool) (c0 : Fin (X.m + 1)) :
    baseExp C0 CE1 CE2 X j b ((topOdd X j i0, β0), c0) = (if β0 then b.rz i0 c0 else b.ry i0 c0) +
      (if (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma ∧ c0 = 0 then (X.seg C0 CE1 CE2 j).P X.p i0 *
        (if β0 then coarseA X.p (X.seg C0 CE1 CE2 j) b i0 - b.w i0 else b.sg i0) else 0) := by
  classical
  have hinj := topOdd_inj X j
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  have hne : ∀ (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)), i ≠ i0 →
      ((topOdd X j i, β), c) ≠ ((topOdd X j i0, β0), c0) := by
    intro i β c hi h
    exact hi (hinj (congrArg (fun y => y.1.1) h))
  rw [baseExp, Finsupp.add_apply]
  congr 1
  · rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i0]
    · rw [Finsupp.finset_sum_apply, Finset.sum_eq_single c0]
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
        cases β0 <;> simp
      · intro c _ hc
        rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg, if_neg]
        · rfl
        · intro h
          exact hc (congrArg (fun y => y.2) h)
        · intro h
          exact hc (congrArg (fun y => y.2) h)
      · intro h
        exact absurd (Finset.mem_univ c0) h
    · intro i _ hi
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true c hi),
        if_neg (hne i false c hi)]
      rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h
  · rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i0]
    · rw [hite]
      by_cases h1 : (i0 : ℕ) < (X.seg C0 CE1 CE2 j).sigma
      · by_cases hc : c0 = 0
        · subst hc
          rw [if_pos h1, if_pos ⟨h1, rfl⟩, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
          cases β0 <;> simp
        · rw [if_pos h1, if_neg (fun h => hc h.2), Finsupp.add_apply, Finsupp.single_apply,
            Finsupp.single_apply, if_neg, if_neg]
          · rfl
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
          · intro h
            exact hc (congrArg (fun y => y.2) h).symm
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    · intro i _ hi
      rw [hite]
      split_ifs
      · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (hne i true 0 hi),
          if_neg (hne i false 0 hi)]
        rfl
      · rfl
    · intro h
      exact absurd (Finset.mem_univ i0) h

theorem baseExp_end (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (β0 : Bool) (c0 : Fin (X.m + 1)) : baseExp C0 CE1 CE2 X j b ((topEnd X j, β0), c0) = 0 := by
  classical
  have hite : ∀ (Q : Prop) [Decidable Q] (f : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ) (y),
      (if Q then f else 0) y = if Q then f y else 0 := by
    intro Q _ f y
    split_ifs <;> rfl
  simp [baseExp, Finsupp.finset_sum_apply, Finsupp.single_apply, topOdd_ne_end, hite]

end Formalism.MainNotions.ColumnSystems.Pf
