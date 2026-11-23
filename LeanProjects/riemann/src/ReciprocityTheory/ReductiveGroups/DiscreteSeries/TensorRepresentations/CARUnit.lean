import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rhoC_mul_sign_sum (ε : Fin n → Bool) (g : Bool → ℝ) :
    ∑ a, rhoC ε a * g (ε a) = 0 := by
  have hT : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then g (ε a) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases h : b < a ∧ ε a = ε b
    · rw [if_pos h, if_pos ⟨h.1, h.2.symm⟩, h.2]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.symm⟩)]
  have e : ∀ a, rhoC ε a * g (ε a) = (∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) -
      ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0)) / 2 := by
    intro a
    unfold rhoC
    rw [natCast_card_filter, natCast_card_filter]
    have e1 : ∑ b, (if a < b ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    have e2 : ∑ b, (if b < a ∧ ε b = ε a then g (ε a) else 0) =
        g (ε a) * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
      rw [mul_sum]; simp [mul_ite]
    rw [e1, e2]; ring
  simp only [e]
  rw [← sum_div, sum_sub_distrib, hT, sub_self, zero_div]

theorem card_same_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 +
      (univ.filter fun b => a < b ∧ ε b = ε a).card := by
  rw [card_filter, card_filter, card_filter,
    show (1:ℕ) = ∑ b : Fin n, if b = a then 1 else 0 by simp, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b a with h | rfl | h
  · simp [h, h.ne, not_lt_of_gt h]
  · simp
  · simp [h, h.ne', not_lt_of_gt h]

theorem card_same_eq (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => ε b = ε a).card = if ε a then pOf ε else qOf ε := by
  cases h : ε a <;> simp [pOf, qOf]

theorem carU_pOf_add_qOf (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  rw [card_filter, card_filter, ← sum_add_distrib]
  have : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [this]

def carUPos (ε : Fin n → Bool) (a : Fin n) : ℕ :=
  (if ε a then 0 else pOf ε) + (univ.filter fun b => b < a ∧ ε b = ε a).card

theorem carUPos_lt (ε : Fin n → Bool) (a : Fin n) : carUPos ε a < n := by
  have h1 := card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 := carU_pOf_add_qOf ε
  unfold carUPos
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> omega

theorem carUPos_injective (ε : Fin n → Bool) : Function.Injective (carUPos ε) := by
  have key : ∀ a a' : Fin n, a < a' → ε a = ε a' → carUPos ε a < carUPos ε a' := by
    intro a a' hlt he
    unfold carUPos
    rw [he]
    have hs : (univ.filter fun b => b < a ∧ ε b = ε a') ⊂ (univ.filter fun b => b < a' ∧ ε b = ε a') := by
      rw [ssubset_iff_of_subset]
      · exact ⟨a, by simp [hlt, he], by simp⟩
      · intro b hb
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact ⟨hb.1.trans hlt, hb.2⟩
    have := card_lt_card hs
    omega
  have key2 : ∀ a a' : Fin n, ε a = true → ε a' = false → carUPos ε a < carUPos ε a' := by
    intro a a' ha ha'
    have h1 := card_same_split ε a
    have h2 := card_same_eq ε a
    unfold carUPos
    simp only [ha, ha', Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢
    omega
  intro a a' hq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · by_cases he : ε a = ε a'
    · exact (key a a' h he).ne hq
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq
  · by_cases he : ε a' = ε a
    · exact (key a' a h he).ne hq.symm
    · cases ha : ε a <;> cases ha' : ε a' <;> simp_all
      · exact (key2 a' a ha' ha).ne hq.symm
      · exact (key2 a a' ha ha').ne hq

theorem rhoC_add_rhoHol_eq (ε : Fin n → Bool) (a : Fin n) :
    (rhoC ε + rhoHol ε) a = ((n : ℝ) - 1) / 2 - (carUPos ε a : ℝ) := by
  have h1 : ((univ.filter fun b => ε b = ε a).card : ℝ) =
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 +
        ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := by
    exact_mod_cast card_same_split ε a
  have h2 := card_same_eq ε a
  have h3 : (pOf ε : ℝ) + (qOf ε : ℝ) = n := by exact_mod_cast carU_pOf_add_qOf ε
  simp only [Pi.add_apply, rhoC, rhoHol, carUPos]
  cases h : ε a <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at h1 h2 ⊢ <;> rw [h2] at h1 <;> push_cast <;>
    linarith

theorem carU_nsq_add (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq dot
  rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem dot_rhoC_rhoHol (ε : Fin n → Bool) : dot (rhoC ε) (rhoHol ε) = 0 :=
  rhoC_mul_sign_sum ε (fun t => if t then (qOf ε : ℝ) / 2 else -(pOf ε : ℝ) / 2)

theorem nsq_rho_split (ε : Fin n → Bool) : nsq (rho n) = nsq (rhoC ε) + nsq (rhoHol ε) := by
  let σ : Fin n → Fin n := fun a => ⟨carUPos ε a, carUPos_lt ε a⟩
  have hinj : Function.Injective σ := fun a a' h => carUPos_injective ε (congrArg Fin.val h)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  have hval : ∀ a, (rhoC ε + rhoHol ε) a = rho n (σ a) := fun a => rhoC_add_rhoHol_eq ε a
  have hs : nsq (rhoC ε + rhoHol ε) = nsq (rho n) := by
    unfold nsq dot
    simp only [hval]
    exact (Equiv.ofBijective σ hbij).sum_comp (fun b => rho n b * rho n b)
  rw [← hs, carU_nsq_add, dot_rhoC_rhoHol]; ring

section Unitary
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem inner_dOp_left {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hU : IsInfUnitary ε E) (hEC : CommutesCAR E cp cm)
    (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ (dOp ε E cp x) y = inner ℂ x (dOp' ε E cm y) := by
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, sum_inner, inner_neg_right, inner_sum,
    ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  have hc := LinearMap.congr_fun (hEC i a i a).2 y
  simp only [Module.End.mul_apply] at hc ⊢
  rw [hU, hadj, ← hc]
  simp [adjSign, hi, ha]

theorem inner_dOp'_left {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hU : IsInfUnitary ε E) (hEC : CommutesCAR E cp cm)
    (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ (dOp' ε E cm x) y = inner ℂ x (dOp ε E cp y) := by
  have hadj' : ∀ (i a : Fin n) (u v : W), inner ℂ (cm i a u) v = inner ℂ u (cp i a v) := by
    intro i a u v
    rw [← inner_conj_symm, ← hadj i a v u, inner_conj_symm]
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, sum_inner, inner_neg_left, inner_sum,
    ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  have hc := LinearMap.congr_fun (hEC a i i a).1 y
  simp only [Module.End.mul_apply] at hc ⊢
  rw [hU, hadj', hc]
  simp [adjSign, hi, ha]

theorem D_symm {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hU : IsInfUnitary ε E)
    (hEC : CommutesCAR E cp cm) (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ ((dOp ε E cp + dOp' ε E cm) x) y = inner ℂ x ((dOp ε E cp + dOp' ε E cm) y) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    inner_dOp_left hU hEC hadj, inner_dOp'_left hU hEC hadj, add_comm]

end Unitary

section Value
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pair_apply_khw {E : Fin n → Fin n → Module.End ℂ W} {μ : Fin n → ℝ} {v : W} {a b : Fin n}
    (hc : E a b * E b a - E b a * E a b = E a a - E b b) (hd : ∀ a, E a a v = (μ a : ℂ) • v)
    (hab : a < b → E a b v = 0) (hba : b < a → E b a v = 0) :
    (E a b * E b a) v = ((hwTerm μ a b : ℝ) : ℂ) • v := by
  unfold hwTerm
  rcases lt_trichotomy a b with h | rfl | h
  · have hc' : E a b * E b a = E b a * E a b + (E a a - E b b) := by
      rw [← hc]; abel
    rw [hc']
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, hab h, map_zero,
      hd, zero_add, if_neg h.ne, if_pos h]
    push_cast
    rw [sub_smul]
  · simp only [Module.End.mul_apply, hd, map_smul, smul_smul, if_true]
    push_cast; ring_nf
  · simp [Module.End.mul_apply, hba h, h.ne', not_lt_of_gt h]

theorem casimirK_khwVec_compact (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ W}
    (hE : ∀ a b, ε a = ε b → E a b * E b a - E b a * E a b = E a a - E b b)
    {μ : Fin n → ℝ} {v : W} (hv : IsKHWVec ε E μ v) :
    casimirK ε E v = ((nsq (μ + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • v := by
  have hsum : casimirK ε E v =
      ((∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), hwTerm μ a b : ℝ) : ℂ) • v := by
    unfold casimirK
    simp only [LinearMap.sum_apply]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact pair_apply_khw (hE a b hb.symm) hv.1 (fun h => hv.2 a b h hb.symm) (fun h => hv.2 b a h hb)
  rw [hsum]
  congr 3
  exact sum_hwTerm (fun a b : Fin n => ε b = ε a) (fun _ => rfl) (fun a b h => h.symm) μ (rhoC ε)
    (fun a => by unfold rhoC; ring)

theorem E_comm_sgE {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E a b * sgE ε cp cm c d = sgE ε cp cm c d * E a b := by
  have h1 : ∀ i j k l, E a b * (cp i j * cm k l) = (cp i j * cm k l) * E a b := by
    intro i j k l
    rw [← mul_assoc, (hEC a b i j).1, mul_assoc, (hEC a b k l).2, mul_assoc]
  unfold sgE
  split_ifs
  · rw [mul_sum, sum_mul]; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · rw [mul_neg, neg_mul, mul_sum, sum_mul]; congr 1; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · simp

theorem diagE_compact {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) (a b : Fin n) (h : ε a = ε b) :
    diagE ε E cp cm a b * diagE ε E cp cm b a - diagE ε E cp cm b a * diagE ε E cp cm a b =
      diagE ε E cp cm a a - diagE ε E cp cm b b := by
  have e1 := hE a b b a
  have e2 := sgE_comm hC ε a b b a h h.symm
  simp only [if_true] at e1 e2
  rw [sub_eq_iff_eq_add] at e1 e2
  unfold diagE
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, E_comm_sgE hEC ε a b b a,
    E_comm_sgE hEC ε b a a b, e1, e2]
  abel

theorem khw_real_identity (ε : Fin n → Bool) (δ : Fin n → ℝ) :
    nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) =
      nsq (δ + rhoC ε) - nsq (rho n) := by
  rw [nsq_rho_split ε]
  have h0 := dot_rhoC_rhoHol ε
  have : nsq (δ + rhoHol ε + rhoC ε) - nsq (rhoC ε) - 2 * dot (rhoHol ε) (δ + rhoHol ε) -
      (nsq (δ + rhoC ε) - (nsq (rhoC ε) + nsq (rhoHol ε))) = 2 * dot (rhoC ε) (rhoHol ε) := by
    unfold nsq dot
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply]; ring
  rw [h0] at this
  linarith

theorem two_D_sq_khw {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E)
    (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) {δ : Fin n → ℝ} {v : W}
    (hv : IsKHWVec ε (diagE ε E cp cm) (δ + rhoHol ε) v) {c : ℂ} (hc : casimir E v = c • v) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) v =
      (((nsq (δ + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - c) • v := by
  have hK := casimirK_khwVec_compact ε (diagE_compact hE hC hEC ε) hv
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a v =
      ((dot (rhoHol ε) (δ + rhoHol ε) : ℝ) : ℂ) • v := by
    simp only [hv.1, smul_smul, ← sum_smul]
    congr 1
    unfold dot
    push_cast
    rfl
  rw [← LinearMap.smul_apply, two_D_sq hE hC hEC ε]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hc, hK, hs]
  rw [← khw_real_identity ε δ]
  simp only [smul_smul, sub_smul]
  push_cast
  simp only [sub_smul, mul_smul]
  abel

end Value

end ReciprocityTheory.ChartRestriction.DS
