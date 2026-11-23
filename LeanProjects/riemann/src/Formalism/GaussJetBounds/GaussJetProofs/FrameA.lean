import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementK
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem frameA_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero,
      norm_zero]
    exact norm_nonneg _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hV : ‖∑ b ∈ S, U b‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)
    obtain ⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) =
        U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by
      refine ⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖U a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU a)
      have h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
      have h3 := IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)
      calc ‖U a‖ ^ k * ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) * ‖(((l ^ e).choose k / l : ℕ) : K)‖
          ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) =
        ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R := by
      rw [hReq]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖R‖ ≤ ‖(l : K)‖ * 1 := by gcongr
      _ = ‖(l : K)‖ := mul_one _

theorem frameA_letter {K : Type u} [NormedField K] [IsUltrametricDist K] (J N0 : ℕ)
    (lam : Fin J → Fin N0 → K) (y : Fin N0 → Fin N0 → K) (hlam : ∀ i a, ‖lam i a‖ ≤ 1)
    (hy : ∀ k a, ‖y k a‖ ≤ 1) (e : Fin J → Fin N0) (he : Function.Injective e)
    (top : Fin N0 → Prop) [DecidablePred top] (htop : ∀ i, ¬ top (e i))
    (hdet : ‖(Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a).det‖ = 1) :
    ∃ (x T : Fin N0 → Fin N0 → K), (∀ k a, ‖x k a‖ ≤ 1) ∧ (∀ i k, ‖T i k‖ ≤ 1) ∧
      (∀ k a, top k → x k a = y k a) ∧
      (∀ i a, ¬ top i → y i a = ∑ k, (if top k then 0 else T i k) * x k a) ∧
      (∀ i k, ¬ top k → k ≠ e i → ∑ a, lam i a * x k a = 0) := by
  classical
  set A : Matrix (Fin J) (Fin J) K := Matrix.of fun (i i' : Fin J) => ∑ a, lam i a * y (e i') a
    with hA
  let c : Fin N0 → Fin J → K := fun k i => ∑ a, lam i a * y k a
  have hc : ∀ k i, ‖c k i‖ ≤ 1 := fun k i =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => by
      rw [norm_mul]; exact mul_le_one₀ (hlam i a) (norm_nonneg _) (hy k a))
  have hAc : ∀ i i', A i i' = c (e i') i := fun _ _ => rfl
  have hAint : ∀ i i', ‖A i i'‖ ≤ 1 := fun i i' => hc _ _
  have hAinv : ∀ i i', ‖A⁻¹ i i'‖ ≤ 1 := norm_inv_entry_le_one A hAint hdet
  have hne : A.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  let z : Fin J → Fin N0 → K := fun i' a => ∑ i'', A⁻¹ i'' i' * y (e i'') a
  have hz : ∀ i a, ‖z i a‖ ≤ 1 := fun i a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i'' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hAinv _ _) (norm_nonneg _) (hy _ _))
  have hcz : ∀ k a, ‖∑ i', c k i' * z i' a‖ ≤ 1 := fun k a =>
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun i' _ => by
      rw [norm_mul]; exact mul_le_one₀ (hc _ _) (norm_nonneg _) (hz _ _))

  have hlz : ∀ i i', ∑ a, lam i a * z i' a = if i = i' then 1 else 0 := by
    intro i i'
    have h1 : ∑ a, lam i a * z i' a = ∑ i'', A i i'' * A⁻¹ i'' i' := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i'' _ => ?_)
      rw [hAc]
      simp only [c, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [h1, ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hunit, Matrix.one_apply]

  have hzy : ∀ i'' a, ∑ i', c (e i'') i' * z i' a = y (e i'') a := by
    intro i'' a
    have h1 : ∑ i', c (e i'') i' * z i' a = ∑ m, (∑ i', A⁻¹ m i' * A i' i'') * y (e m) a := by
      simp only [z, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun i' _ => ?_))
      rw [hAc]; ring
    rw [h1]
    simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
    simp
  let x : Fin N0 → Fin N0 → K := fun k a =>
    if top k then y k a else if h : ∃ i, e i = k then z h.choose a
      else y k a - ∑ i', c k i' * z i' a
  let T : Fin N0 → Fin N0 → K := fun i k =>
    (if (∃ i', e i' = i) then 0 else if k = i then 1 else 0) + ∑ i', if k = e i' then c i i' else 0
  have hxe : ∀ i a, x (e i) a = z i a := by
    intro i a
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    have hch : hex.choose = i := he hex.choose_spec
    simp only [x]
    rw [if_neg (htop i), dif_pos hex, hch]
  have hxn : ∀ k a, ¬ top k → (¬ ∃ i, e i = k) → x k a = y k a - ∑ i', c k i' * z i' a := by
    intro k a h1 h2
    simp only [x]
    rw [if_neg h1, dif_neg h2]
  have hsumT : ∀ i k, (∑ i', if k = e i' then c i i' else 0) = 0 ∨
      ∃ i', (∑ i', if k = e i' then c i i' else 0) = c i i' := by
    intro i k
    by_cases h : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h
      right
      refine ⟨i0, ?_⟩
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (he h).symm)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · left
      refine Finset.sum_eq_zero (fun i' _ => ?_)
      rw [if_neg (fun hk => h ⟨i', hk.symm⟩)]
  refine ⟨x, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro k a
    by_cases h1 : top k
    · simp only [x]; rw [if_pos h1]; exact hy _ _
    · by_cases h2 : ∃ i, e i = k
      · obtain ⟨i, rfl⟩ := h2
        rw [hxe]; exact hz _ _
      · rw [hxn k a h1 h2, sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy _ _) ?_)
        rw [norm_neg]; exact hcz _ _
  · intro i k
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs <;> simp
    · rcases hsumT i k with h | ⟨i', h⟩
      · rw [h]; simp
      · rw [h]; exact hc _ _
  · intro k a h1
    simp only [x]; rw [if_pos h1]
  · intro i a hi
    have hT0 : ∀ k, (if top k then 0 else T i k) = T i k := by
      intro k
      split_ifs with hk
      · symm
        have h1 : k ≠ i := fun h => hi (h ▸ hk)
        have h2 : (∑ i', if k = e i' then c i i' else 0) = 0 :=
          Finset.sum_eq_zero (fun i' _ => by
            rw [if_neg (fun h : k = e i' => htop i' (h ▸ hk))])
        simp only [T]
        rw [h2, if_neg h1]
        simp
      · rfl
    simp only [hT0]
    have hsecond : ∑ k, (∑ i', if k = e i' then c i i' else 0) * x k a = ∑ i', c i i' * z i' a := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Finset.sum_eq_single (e i')]
      · rw [if_pos rfl, hxe]
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [T, add_mul, Finset.sum_add_distrib]
    rw [hsecond]
    by_cases h2 : ∃ i', e i' = i
    · simp only [if_pos h2, zero_mul, Finset.sum_const_zero, zero_add]
      obtain ⟨i0, rfl⟩ := h2
      exact (hzy i0 a).symm
    · simp only [if_neg h2]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hxn i a hi h2]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
  · intro i k hk hne'
    by_cases h2 : ∃ i', e i' = k
    · obtain ⟨i0, rfl⟩ := h2
      simp only [hxe]
      rw [hlz, if_neg (fun h : i = i0 => hne' (h ▸ rfl))]
    · simp only [hxn k _ hk h2, mul_sub, Finset.sum_sub_distrib]
      have h3 : ∑ a, lam i a * ∑ i', c k i' * z i' a = ∑ i', c k i' * ∑ a, lam i a * z i' a := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i' _ => Finset.sum_congr rfl (fun a _ => by ring))
      rw [h3]
      simp only [hlz]
      simp [c]

theorem thmAFrame_of : ThmAGen.{u} → ThmAFrame.{u} := by
  intro hGen K _ _ _ l d N0 N1 _ hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I xg hxg nu1 nu2 size hnu1 hnu2 hsize a ha hsa J lab hlabinj hlab lam hlam hlampos hlamneg
    e he hetop hdet
  classical
  have hL := fun s : ZMod d => frameA_letter (J s) N0 (lam s) (fun k a => xg (s, k, a)) (hlam s)
    (fun k a => hxg _) (e s) (he s) (fun k => s ∈ TT ∧ k.val = 0) (hetop s) (hdet s)
  choose xs T hxs hT hxtop hrec hdual using hL
  let x : ZMod d × Fin N0 × Fin N0 → K := fun y => xs y.1 y.2.1 y.2.2
  let spec : ZMod d × Fin N0 → Option (ZMod d × ℤ) := fun r =>
    if h : ∃ i, e r.1 i = r.2 then some (lab r.1 h.choose) else none
  have hspec_e : ∀ s i, spec (s, e s i) = some (lab s i) := by
    intro s i
    have hex : ∃ i', e s i' = e s i := ⟨i, rfl⟩
    have hch : hex.choose = i := he s hex.choose_spec
    show (if h : ∃ i', e s i' = e s i then some (lab s h.choose) else none) = _
    rw [dif_pos hex, hch]
  have hspec_some : ∀ s k, spec (s, k) ≠ none → ∃ i, k = e s i := by
    intro s k h
    by_contra hcon
    apply h
    show (if h : ∃ i', e s i' = k then some (lab s h.choose) else none) = _
    rw [dif_neg (fun ⟨i, hi⟩ => hcon ⟨i, hi.symm⟩)]
  refine hGen K l d N0 N1 hl hl3 hd hde hlK h0 K0 hK0 ζ hζ be hbe x (fun y => hxs _ _ _) g hg0 hg U hU
    ε hε TT colN p hp hp1 I T hT xg ?_ nu1 nu2 size hnu1 hnu2 hsize a ha hsa spec ?_ ?_ ?_
  · intro s i b
    by_cases hi : s ∈ TT ∧ i.val = 0
    · simp only [effMat, if_pos hi]
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul]
        exact (hxtop s i b hi).symm
      · intro k _ hk
        rw [if_neg hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [effMat, if_neg hi]
      exact hrec s i b hi
  · intro s k s0 j hsp
    obtain ⟨i, rfl⟩ := hspec_some s k (by rw [hsp]; simp)
    rw [hspec_e] at hsp
    have hlb : lab s i = (s0, j) := Option.some.inj hsp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (hlab s s0 j).mp ⟨i, hlb⟩
    exact ⟨h1, h2, h3, hetop s i, h4, h5⟩
  · rintro ⟨s, k⟩ ⟨s', k'⟩ hne heq
    obtain ⟨i, rfl⟩ := hspec_some s k hne
    obtain ⟨i', rfl⟩ := hspec_some s' k' (by rw [← heq]; exact hne)
    rw [hspec_e, hspec_e] at heq
    have hlb : lab s i = lab s' i' := Option.some.inj heq
    have e1 := ((hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩).2.2.1
    have e2 := ((hlab s' (lab s' i').1 (lab s' i').2).mp ⟨i', rfl⟩).2.2.1
    have hss : s = s' := by rw [e1, e2, hlb]
    subst hss
    have hii : i = i' := hlabinj s hlb
    rw [hii]
  · intro s0 hs0 s k j hk hj hs hpos hneg hsp
    obtain ⟨i, hi⟩ := (hlab s s0 j).mpr ⟨hs0, hj, hs, hpos, hneg⟩
    have hki : k ≠ e s i := by
      intro h
      apply hsp
      rw [h, hspec_e, hi]
    have hzero : ∑ b, lam s i b * xs s k b = 0 := hdual s i k hk hki
    have hx0 : ∀ b, x (s0, ⟨0, h0⟩, b) = xg (s0, ⟨0, h0⟩, b) := fun b =>
      hxtop s0 ⟨0, h0⟩ b ⟨hs0, rfl⟩
    have hi1 : (lab s i).1 = s0 := by rw [hi]
    have hi2 : (lab s i).2 = j := by rw [hi]
    split_ifs with hj0
    · have hjpos : 0 < j := by
        rcases hj with ⟨m, hm⟩
        omega
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) ^ (l ^ j.toNat) = lam s i b := by
        intro b
        have := hlampos s i b (by rw [hi2]; exact hjpos)
        rw [hi1, hi2] at this
        rw [this, hx0]
      simp only [hl1]
      show ‖∑ b, lam s i b * xs s k b‖ ≤ _
      rw [hzero, norm_zero]
      exact norm_nonneg _
    · have hjneg : j < 0 := not_le.mp hj0
      have hl1 : ∀ b, x (s0, ⟨0, h0⟩, b) = lam s i b ^ (l ^ (-j).toNat) := by
        intro b
        have := hlamneg s i b (by rw [hi2]; exact hjneg)
        rw [hi1, hi2] at this
        rw [this, hx0]
      have hfr := frameA_frob_norm (K := K) hl (fun b => lam s i b * xs s k b) (fun b => by
        rw [norm_mul]; exact mul_le_one₀ (hlam s i b) (norm_nonneg _) (hxs s k b)) (-j).toNat
        Finset.univ
      rw [hzero, zero_pow (pow_ne_zero _ hl.ne_zero), zero_sub, norm_neg] at hfr
      simp only [hl1]
      show ‖∑ b, lam s i b ^ (l ^ (-j).toNat) * xs s k b ^ (l ^ (-j).toNat)‖ ≤ _
      simpa only [mul_pow] using hfr

theorem theorem_A_frame : ThmAFrame.{u} := thmAFrame_of thmAGen

end Formalism.DworkPowerSeriesWeights
