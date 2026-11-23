import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem val_digit {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (μ : σ → ℕ) :
    (∏ v, (ρ v + L v * μ v).factorial).factorization p =
      (∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v)).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, -⟩ := h2 σ t' ρ' hlt
  set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
  set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
  have hU0 : U ≠ 0 := (hunit e').1
  have hUv : padicValRat p U = 0 := (hunit e').2
  have key : ((∏ v, (ρ v + L v * μ v).factorial : ℕ) : ℚ) =
      ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) * U := by
    push_cast
    rw [hU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : odd v
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_pos hv] at this ⊢
      rw [(hodd v hv).1, this]
      ring
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_neg hv] at this ⊢
      rw [(hend v hv).1, (hend v hv).2]
      simp only [zero_add, mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, zero_add] at this ⊢
      rw [← this]
      simp
  have hQ0 : ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.2 fun v _ =>
      mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hv := congrArg (padicValRat p) key
  rw [padicValRat.mul hQ0 hU0, hUv, add_zero, padicValRat.of_nat, padicValRat.of_nat] at hv
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact_mod_cast hv

def tdeg (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (x : X.TT × Bool) : ℕ :=
  multideg (ioExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b)) x

def TrueDegAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∏ x : X.TT × Bool, (tdeg C0 CE1 CE2 X j b x).factorial = facSeg X j ∧
      ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) = lgSeg X j

def CoarseMultAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p ≤
        (expFact (mu0 C0 CE1 CE2 X j b)).factorization X.p + lgSeg X j

theorem kapNumAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hT : TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  obtain ⟨hT1, hT2⟩ := hT X hD1 hH hc j b hb
  have hM1 := hM X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b

  obtain ⟨M, hM0, hEM, hMv⟩ := expFact_mul X.p (tdeg C0 CE1 CE2 X j b) (ioExp C0 CE1 CE2 X j b μ0) (fun x => rfl)
  rw [hT1] at hEM
  have hMv' : M.factorization X.p ≤ X.m * lgSeg X j := by
    rw [← hT2, Finset.mul_sum]
    refine hMv.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    simp

  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  have hvd := val_digit h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) μ0
  have hE0 : expFact (ioExp C0 CE1 CE2 X j b μ0) ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hmu0 : expFact μ0 = ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
  have hR0 : Rblk C0 CE1 CE2 X j b ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP1 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
      symLev X.p C0 CE1 CE2 X j v * μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP2 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hP3 : (∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hsplit : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (μ0 v).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) =
      (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
        (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) * ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hvE : (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p =
      (PhiB C0 CE1 CE2 X j b).factorization X.p + (expFact μ0).factorization X.p := by
    rw [expFact_ioExp, Nat.factorization_mul hR0 hP1, Finsupp.add_apply, hvd, hsplit, Nat.factorization_mul hP2 hP3,
      Finsupp.add_apply, hmu0]
    unfold PhiB
    rw [Nat.factorization_mul hR0 hP2, Finsupp.add_apply]
    ring
  have hvF : (facSeg X j).factorization X.p = (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p +
      M.factorization X.p := by
    rw [← hEM, Nat.factorization_mul hE0 hM0, Finsupp.add_apply]

  have hdv : expFact μ0 ∣ ∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial := by
    have h := dvdAt C0 CE1 CE2 X j b hb μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b)
    unfold Nblk at h
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (specConst_ne _ _ _)) h
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hle : (expFact μ0).factorization X.p ≤ (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p :=
    (Nat.factorization_le_iff_dvd (by rw [hmu0]; exact hP3) hc0).2 hdv X.p
  constructor
  · rw [hvF, hvE]
    have : X.m * lgSeg X j ≤ (X.m + 1) * lgSeg X j := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  · rw [hvF, hvE]
    omega

end Formalism.MainNotions.ColumnSystems.Pf
