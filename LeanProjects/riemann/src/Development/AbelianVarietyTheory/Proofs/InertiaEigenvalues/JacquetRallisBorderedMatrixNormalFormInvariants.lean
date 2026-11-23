import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

def ev (r : ℕ) (k : Type) [Field k] (i : ℕ) : Fin r → k := fun j => if (j : ℕ) = i then 1 else 0

theorem ev_eq_single (i : ℕ) (hi : i < r) : ev r k i = Pi.single (⟨i, hi⟩ : Fin r) 1 := by
  funext j
  simp only [ev, Pi.single_apply, Fin.ext_iff]

theorem sum_mulVec' {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, ih]

theorem pow_card_eq (M : Matrix (Fin r) (Fin r) k) :
    M ^ r = - ∑ l ∈ Finset.range r, M.charpoly.coeff l • M ^ l := by
  have h0 := aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range, charpoly_natDegree_eq_dim, Fintype.card_fin,
    Finset.sum_range_succ] at h0
  have h1 : M.charpoly.coeff r = 1 := by
    have := (charpoly_monic M).leadingCoeff
    rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at this
  rw [h1, one_smul] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

theorem companion_mulVec_ev (p : Fin r → k) (i : ℕ) (hi : i + 1 < r) :
    companion p *ᵥ ev r k i = ev r k (i + 1) := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp only [mulVec_single, companion, of_apply, mul_one, ev]
  have : ¬ (i + 1 = r) := by omega
  simp [this]

theorem companion_mulVec_last (p : Fin r → k) (i : ℕ) (hi : i + 1 = r) :
    companion p *ᵥ ev r k i = - p := by
  rw [ev_eq_single i (by omega)]
  funext j
  simp [mulVec_single, companion, hi]

theorem companion_pow_ev (p : Fin r → k) (i : ℕ) (hi : i < r) :
    companion p ^ i *ᵥ ev r k 0 = ev r k i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_ev p i hi]

theorem companion_pow_card (p : Fin r → k) (hr : 0 < r) :
    companion p ^ r *ᵥ ev r k 0 = - p := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ', ← mulVec_mulVec, companion_pow_ev p m (by omega), companion_mulVec_last p m rfl]

theorem charpoly_companion_coeff (p : Fin r → k) (i : Fin r) :
    (companion p).charpoly.coeff i = p i := by
  have hr : 0 < r := i.pos
  have h := pow_card_eq (companion p)
  have h2 := congrArg (fun M => M *ᵥ ev r k 0) h
  simp only [companion_pow_card p hr, neg_mulVec, sum_mulVec', smul_mulVec] at h2
  have h3 := congrFun h2 i
  simp only [Pi.neg_apply, neg_inj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, Finset.sum_eq_single (i : ℕ)]
  · simp [companion_pow_ev p i i.2, ev]
  · intro b hb hne
    rw [companion_pow_ev p b (Finset.mem_range.mp hb)]
    simp [ev, Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr i.2) h

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem inv_act' (g : GL (Fin r) k) (Y : Gl r k) : inv (act g Y) = inv Y := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [inv, act, mom, Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · funext i
    rw [Matrix.coe_units_inv, charpoly_units_conj]
  · funext i
    rw [Units.conj_pow, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    congr 2
    simp [mul_assoc]

theorem act_mul' (g h : GL (Fin r) k) (Y : Gl r k) : act (g * h) Y = act g (act h Y) := by
  obtain ⟨A, b, c, l⟩ := Y
  simp only [act, _root_.mul_inv_rev, Units.val_mul, mulVec_mulVec, vecMul_vecMul, Prod.mk.injEq, and_true]
  try simp [mul_assoc]

theorem inv_sec' (a : Inv r k) : inv (sec a) = a := by
  obtain ⟨p, m, l⟩ := a
  simp only [inv, sec, Prod.mk.injEq, and_true]
  refine ⟨funext fun i => charpoly_companion_coeff p i, funext fun i => ?_⟩
  have he : (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) = ev r k 0 := rfl
  simp only [mom, he, companion_pow_ev p i i.2, ev_eq_single (i : ℕ) i.2, dotProduct_single, mul_one]

theorem charpoly_companion_inv (Y : Gl r k) : (companion (inv Y).1).charpoly = Y.1.charpoly := by
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n r with h | h | h
  · exact charpoly_companion_coeff _ ⟨n, h⟩
  · subst h
    have h1 := (charpoly_monic (companion (inv Y).1)).leadingCoeff
    have h2 := (charpoly_monic Y.1).leadingCoeff
    rw [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin] at h1 h2
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt] <;>
      simpa using h

theorem dot_pow_eq_sum (M : Matrix (Fin r) (Fin r) k) (hr : 0 < r) (b c : Fin r → k) (n : ℕ) :
    c ⬝ᵥ (M ^ n *ᵥ b) = ∑ i ∈ Finset.range r,
      ((Polynomial.X ^ n) %ₘ M.charpoly).coeff i * (c ⬝ᵥ (M ^ i *ᵥ b)) := by
  have hmon := charpoly_monic M
  have hdeg : M.charpoly.natDegree = r := by simp
  have hne : M.charpoly ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hdeg; omega
  have hM : M ^ n = Polynomial.aeval M ((Polynomial.X ^ n) %ₘ M.charpoly) := by
    rw [Polynomial.aeval_modByMonic_eq_self_of_root (aeval_self_charpoly M)]
    simp
  rw [hM, Polynomial.aeval_eq_sum_range' (n := r)
    (by have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ n) hmon hne; omega), sum_mulVec', dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem mom_sec_inv (Y : Gl r k) (n : ℕ) : mom (sec (inv Y)) n = mom Y n := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [mom, dotProduct]
  have hs := inv_sec' (inv Y)
  simp only [mom]
  rw [dot_pow_eq_sum _ hr, dot_pow_eq_sum _ hr]
  have hc : (sec (inv Y)).1.charpoly = Y.1.charpoly := charpoly_companion_inv Y
  rw [hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have := congrFun (congrArg (fun a : Inv r k => a.2.1) hs) ⟨i, Finset.mem_range.mp hi⟩
  simpa [inv, mom] using this

theorem hankel_eq (Y : Gl r k) : Cm Y * Bm Y = hankel (inv Y) := by
  ext i j
  simp only [mul_apply, Cm, Bm, hankel, of_apply, mom_sec_inv]
  simp only [mom]
  rw [pow_add, ← mulVec_mulVec, dotProduct_mulVec]
  rfl

end GlobalTheory.JR.NormalFormL

namespace GlobalTheory.JR.NormalFormL

variable {k : Type} [Field k] {r : ℕ}

theorem mul_Bm (Y : Gl r k) : Y.1 * Bm Y = Bm Y * companion (inv Y).1 := by
  ext i j
  have hl : (Y.1 * Bm Y) i j = (Y.1 ^ ((j : ℕ) + 1) *ᵥ Y.2.1) i := by
    rw [pow_succ', ← mulVec_mulVec]
    simp [mul_apply, Bm, mulVec, dotProduct]
  rw [hl, mul_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · simp only [companion, of_apply, hj, if_true, Bm, inv]
    rw [pow_card_eq Y.1, neg_mulVec, sum_mulVec']
    simp only [Pi.neg_apply, Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun l => (Y.1 ^ l *ᵥ Y.2.1) i * -Y.1.charpoly.coeff l),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  · have hj' : (j : ℕ) + 1 < r := by omega
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj'⟩ : Fin r)]
    · simp [companion, hj, Bm]
    · intro l _ hne
      have : ¬ ((l : ℕ) = (j : ℕ) + 1) := fun h => hne (Fin.ext h)
      simp [companion, hj, this]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem vecMul_Bm (Y : Gl r k) : Y.2.2.1 ᵥ* Bm Y = (inv Y).2.1 := by
  funext j
  simp [vecMul, dotProduct, Bm, inv, mom, mulVec]

theorem det_Bm_ne (Y : Gl r k) (h : Delta (inv Y) ≠ 0) : (Bm Y).det ≠ 0 := by
  intro h0
  apply h
  rw [Delta, ← hankel_eq, det_mul, h0, mul_zero]

theorem unique_conj (Y Y₁ : Gl r k) (hΔ : Delta (inv Y) ≠ 0) (hI : inv Y₁ = inv Y) :
    ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  have hB : IsUnit (Bm Y) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y hΔ))
  have hB₁ : IsUnit (Bm Y₁) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_Bm_ne Y₁ (hI ▸ hΔ)))
  set u := hB.unit with hu
  set u₁ := hB₁.unit with hu₁
  have eu : (u : Matrix (Fin r) (Fin r) k) = Bm Y := hB.unit_spec
  have eu₁ : (u₁ : Matrix (Fin r) (Fin r) k) = Bm Y₁ := hB₁.unit_spec
  refine ⟨u₁ * u⁻¹, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨A, b, c, l⟩ := Y
    obtain ⟨A₁, b₁, c₁, l₁⟩ := Y₁
    have hAB := mul_Bm (A, b, c, l)
    have hAB₁ := mul_Bm (A₁, b₁, c₁, l₁)
    have hc := vecMul_Bm (A, b, c, l)
    have hc₁ := vecMul_Bm (A₁, b₁, c₁, l₁)
    rw [hI] at hAB₁ hc₁
    rw [← eu] at hAB hc
    rw [← eu₁] at hAB₁ hc₁
    have hl : l₁ = l := congrArg (fun a : Inv r k => a.2.2) hI
    simp only [act, _root_.mul_inv_rev, inv_inv, Units.val_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, hl.symm⟩
    · calc (u₁ : Matrix (Fin r) (Fin r) k) * ↑u⁻¹ * A * (↑u * ↑u₁⁻¹)
            = ↑u₁ * (↑u⁻¹ * (A * ↑u)) * ↑u₁⁻¹ := by simp only [mul_assoc]
          _ = ↑u₁ * companion (inv (A, b, c, l)).1 * ↑u₁⁻¹ := by
            rw [hAB, Units.inv_mul_cancel_left]
          _ = A₁ := by rw [← hAB₁, Units.mul_inv_cancel_right]
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; funext i; exact i.elim0
      have e0 : ∀ (B : Matrix (Fin r) (Fin r) k) (Z : Gl r k), B = Bm Z →
          B *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = Z.2.1 := by
        intro B Z hBZ; subst hBZ; funext i; simp [mulVec_single, Bm]
      have hb : (u : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b :=
        e0 _ (A, b, c, l) eu
      have hb₁ : (u₁ : Matrix (Fin r) (Fin r) k) *ᵥ Pi.single (⟨0, hr⟩ : Fin r) 1 = b₁ :=
        e0 _ (A₁, b₁, c₁, l₁) eu₁
      rw [← hb, mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one, hb₁]
    · have hc' : c ᵥ* (u : Matrix (Fin r) (Fin r) k) = c₁ ᵥ* (u₁ : Matrix (Fin r) (Fin r) k) :=
        hc.trans hc₁.symm
      rw [← vecMul_vecMul, hc', vecMul_vecMul, Units.mul_inv, vecMul_one]
  · rw [Units.val_mul, mul_assoc, eu.symm, Units.inv_mul, mul_one, eu₁]
  · rintro g ⟨_, hg⟩
    apply Units.ext
    rw [Units.val_mul, eu₁, ← hg, ← eu, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.JR.NormalFormL

theorem GlobalTheory.JR.normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  intro k _ r
  exact ⟨GlobalTheory.JR.NormalFormL.inv_act', GlobalTheory.JR.NormalFormL.inv_sec', GlobalTheory.JR.NormalFormL.hankel_eq,
    GlobalTheory.JR.NormalFormL.act_mul', GlobalTheory.JR.NormalFormL.unique_conj⟩
