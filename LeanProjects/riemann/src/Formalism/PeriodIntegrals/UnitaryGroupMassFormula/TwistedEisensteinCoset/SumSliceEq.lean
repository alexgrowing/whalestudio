import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.WeightedSumScaling

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE Function

variable {E K : Type} [Field E] [NumberField E] [Field K]

section Slice

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_slice (k : ι) (S : ι → Finset E) (u0 : E) (F : (ι → E) → K) :
    ∑ t ∈ Fintype.piFinset S, F t =
      ∑ t ∈ Fintype.piFinset (update S k {u0}), ∑ u ∈ S k, F (update t k u) := by
  rw [← Finset.sum_product' (f := fun t u => F (update t k u))]
  refine Finset.sum_nbij' (fun t => (update t k u0, t k)) (fun p => update p.1 k p.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at ht ⊢
    refine ⟨fun i => ?_, ht k⟩
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi, ht i]
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp ⊢
    intro i
    by_cases hi : i = k
    · subst hi; simpa using hp.2
    · simpa [Function.update_of_ne hi] using hp.1 i
  · intro t _
    simp
  · intro p hp
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_product] at hp
    have h1 : p.1 k = u0 := by simpa using hp.1 k
    refine Prod.ext ?_ ?_
    · show update (update p.1 k p.2) k u0 = p.1
      rw [Function.update_idem, ← h1, Function.update_eq_self]
    · simp
  · intro t _
    simp

theorem sum_slice_eq (k : ι) (S : ι → Finset E) (T T' : Finset E) (F G : (ι → E) → K) (α : K)
    (h : ∀ t : ι → E, ∑ u ∈ T, F (update t k u) = α * ∑ u ∈ T', G (update t k u)) :
    ∑ t ∈ Fintype.piFinset (update S k T), F t = α * ∑ t ∈ Fintype.piFinset (update S k T'), G t := by
  rw [sum_slice k (update S k T) 0 F, sum_slice k (update S k T') 0 G]
  simp only [Function.update_idem, Function.update_self]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => h t

theorem good_slice {P : HeightOneSpectrum (𝓞 E)} {a b : ℕ} {H : (ι → E) → K} (hH : Good P a b H)
    (t : ι → E) (k : ι) : Good1 P a b (fun u => H (update t k u)) := by
  refine ⟨fun u hu => ?_, fun u δ hδ => ?_⟩
  · simpa using hH.1 (update t k u) hu k
  · have h0 : IntAt P 0 :=
      ⟨0, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
    have e : update t k (u + δ) = update t k u + Pi.single k δ := by
      funext l
      by_cases hl : l = k
      · subst hl; simp
      · simp [hl]
    show H (update t k (u + δ)) = H (update t k u)
    rw [e]
    refine hH.2 _ _ fun l => ?_
    by_cases hl : l = k
    · subst hl; simpa using hδ
    · simpa [hl] using h0

end Slice

section Stab

variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq

theorem sum_stab {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) :
    ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ Fintype.card ι *
        ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) a b), H t := by
  classical

  have sumV : ∀ (A' B' : ℕ) (φ : E → K), ∑ u ∈ valsQ E (qOf P) A' B', φ u = Sg P A' B' φ := by
    intro A' B' φ
    unfold valsQ Sg
    rw [Finset.sum_image]
    intro i hi j _ hij
    by_cases hq : ((qOf P : ℕ) : E) ^ A' = 0
    · exfalso
      have h2 := pow_eq_zero_iff'.1 hq
      have hq0 : qOf P = 0 := by exact_mod_cast h2.1
      simp [hq0, h2.2] at hi
    · exact_mod_cast (div_left_inj' hq).1 hij
  have hslice : ∀ (S : ι → Finset E) (k : ι),
      ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) A B)), H t =
        ((qOf P ^ (B - b) : ℕ) : K) * ∑ t ∈ Fintype.piFinset (update S k (valsQ E (qOf P) a b)), H t :=
    fun S k => sum_slice_eq k S _ _ H H _ fun t => by
      rw [sumV, sumV, sg_stab hN hp hq hA hB (good_slice hH t k)]
  have key : ∀ s : Finset ι, ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t =
      ((qOf P ^ (B - b) : ℕ) : K) ^ s.card * ∑ t ∈ Fintype.piFinset
        (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B), H t := by
    intro s
    refine Finset.induction_on s (by simp) ?_
    intro k s hk ih
    rw [ih, Finset.card_insert_of_notMem hk, pow_succ, mul_assoc]
    congr 1
    have e1 : (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) A B) := by
      funext i
      by_cases h : i = k
      · subst h; simp [hk]
      · simp [h]
    have e2 : (fun i => if i ∈ insert k s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) =
        update (fun i => if i ∈ s then valsQ E (qOf P) a b else valsQ E (qOf P) A B) k
          (valsQ E (qOf P) a b) := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e2]
    conv_lhs => rw [e1]
    exact hslice _ k
  simpa using key Finset.univ

include hK in
theorem rs_stab {ι : Type} [Fintype ι] [DecidableEq ι] {a b A B : ℕ} (hA : a ≤ A) (hB : b ≤ B)
    {H : (ι → E) → K} (hH : Good P a b H) : RS P A B H = RS P a b H := by
  unfold RS
  rw [sum_stab hN hp hq hA hB hH, ← mul_assoc, ← mul_pow]
  congr 2
  push_cast
  have hqb : ((qOf P : K)) ^ B = (qOf P : K) ^ b * (qOf P : K) ^ (B - b) := by
    rw [← pow_add, Nat.add_sub_cancel' hB]
  rw [hqb, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hK), mul_one]

end Stab

theorem stab_of (hN : NTAll) : StabP := by
  intro E' K' _ _ _ P hp hq hK ι _ _ a b H hH A B hA hB
  exact rs_stab hN hp hq hK hA hB hH

end PI.TwistedEisensteinNonvanishing.W
