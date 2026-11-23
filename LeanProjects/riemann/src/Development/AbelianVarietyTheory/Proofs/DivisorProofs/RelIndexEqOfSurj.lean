import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowApplyEqZeroOfStrictUpper

open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod.Cayley

theorem relIndex_eq_of_surj {G A : Type} [Group G] [AddGroup A] (H K : Subgroup G) (B D : AddSubgroup A)
    (f : K → D) (hf : Function.Surjective f)
    (h : ∀ u u' : K, (u : G)⁻¹ * u' ∈ H ↔ -(f u : A) + f u' ∈ B) : H.relIndex K = B.relIndex D := by
  have h' : ∀ u u' : K, (QuotientGroup.leftRel (H.subgroupOf K)) u u' ↔
      (QuotientAddGroup.leftRel (B.addSubgroupOf D)) (f u) (f u') := fun u u' => by
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    exact h u u'
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' f fun a b e => (h' a b).1 e) ⟨?_, ?_⟩)
  · intro x y
    refine Quotient.inductionOn₂' x y fun a b e => ?_
    exact Quotient.sound' ((h' a b).2 (Quotient.exact' e))
  · intro x
    refine Quotient.inductionOn' x fun a => ?_
    obtain ⟨b, rfl⟩ := hf a
    exact ⟨Quotient.mk'' b, rfl⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem pow_apply_eq_zero {y : Matrix (Fin n) (Fin n) L} (hy : ∀ i j, j ≤ i → y i j = 0) (k : ℕ) :
    ∀ i j : Fin n, j.val < i.val + k → (y ^ k) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | (apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper ..)

theorem pow_succ_mem {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {y : Matrix (Fin n) (Fin n) L}
    (hy : y ∈ upLat L c) (k : ℕ) : y ^ (k + 1) ∈ upLat L c := by
  induction k with
  | zero => simpa using hy
  | succ k ih => rw [pow_succ]; exact mul_mem_upLat hc.2 ih hy

theorem exists_inv {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {y : Matrix (Fin n) (Fin n) L}
    (hy : y ∈ upLat L c) : ∃ z ∈ upLat L c, (1 + y) * (1 + z) = 1 ∧ (1 + z) * (1 + y) = 1 := by
  have hy' : -y ∈ upLat L c := neg_mem hy
  have h0 : (-y) ^ (n + 1) = 0 := by
    ext i j
    exact pow_apply_eq_zero hy'.1 _ i j (by have := j.2; omega)
  have h1 : (1 + y) * (1 + ∑ k ∈ Finset.range n, (-y) ^ (k + 1)) = 1 := by
    have := mul_neg_geom_sum (-y) (n + 1)
    rw [h0, sub_zero, sub_neg_eq_add, Finset.sum_range_succ', pow_zero, add_comm _ (1 : Matrix (Fin n) (Fin n) L)] at this
    simpa [add_comm] using this
  exact ⟨_, sum_mem fun k _ => pow_succ_mem hc hy' k, h1, mul_eq_one_comm.1 h1⟩

theorem unit_mul_mem {c C : Fin n → Fin n → ℤ} (hI : IsIdealWeight c C) {a b x : Matrix (Fin n) (Fin n) L}
    (ha : a ∈ upLat L c) (hb : b ∈ upLat L c) (hx : x ∈ upLat L C) : (1 + a) * x * (1 + b) ∈ upLat L C := by
  have h1 : (1 + a) * x ∈ upLat L C := by
    rw [add_mul, one_mul]; exact add_mem hx (mul_mem_upLat hI.2.1 ha hx)
  rw [mul_add, mul_one]
  exact add_mem h1 (mul_mem_upLat hI.2.2 h1 hb)

theorem unit_mul_mem_iff {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hI : IsIdealWeight c C)
    {a b x : Matrix (Fin n) (Fin n) L} (ha : a ∈ upLat L c) (hb : b ∈ upLat L c) :
    (1 + a) * x * (1 + b) ∈ upLat L C ↔ x ∈ upLat L C := by
  refine ⟨fun hx => ?_, unit_mul_mem hI ha hb⟩
  obtain ⟨a', ha', -, e1⟩ := exists_inv hc ha
  obtain ⟨b', hb', e2, -⟩ := exists_inv hc hb
  have := unit_mul_mem hI ha' hb' hx
  rwa [← mul_assoc, ← mul_assoc, e1, one_mul, mul_assoc, e2, mul_one] at this

def cay (t : L) (u : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := (1 + t • (u - 1))⁻¹ * (u - 1)

theorem cay_eq {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {t : L} (ht : Valued.v t ≤ 1)
    {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) :
    ∃ z ∈ upLat L c, (1 + t • (u - 1)) * (1 + z) = 1 ∧ (1 + z) * (1 + t • (u - 1)) = 1 ∧
      cay t u = (1 + z) * (u - 1) := by
  obtain ⟨z, hz, e1, e2⟩ := exists_inv hc (smul_mem_upLat ht hu)
  exact ⟨z, hz, e1, e2, by rw [cay, Matrix.inv_eq_right_inv e1]⟩

theorem cay_mem {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {t : L} (ht : Valued.v t ≤ 1)
    {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) : cay t u ∈ upLat L c := by
  obtain ⟨z, hz, -, -, e⟩ := cay_eq hc ht hu
  rw [e, add_mul, one_mul]
  exact add_mem hu (mul_mem_upLat hc.2 hz hu)

theorem cay_skew {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} {t : L} (ht : Valued.v t ≤ 1)
    (hσ : t + σ t = 1) {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (huv : u * adjJ σ u = 1) :
    cay t u ∈ skewJ σ n := by
  obtain ⟨z, -, e1, e2, e⟩ := cay_eq hc ht hu
  have e3 := congrArg (adjJ σ) e2
  rw [adjJ_mul, adjJ_one, adjJ_add, adjJ_smul, adjJ_sub, adjJ_one] at e3
  rw [mem_skewJ, e, adjJ_mul, adjJ_sub, adjJ_one]
  set v := adjJ σ u
  set W := 1 + z
  set W' := adjJ σ W
  have hs : σ t = 1 - t := by linear_combination hσ
  have key : (1 + t • (u - 1)) * (v - 1) = -((u - 1) * (1 + σ t • (v - 1))) := by
    simp only [hs, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, huv]
    module
  calc (v - 1) * W' = W * ((1 + t • (u - 1)) * (v - 1)) * W' := by rw [← mul_assoc W, e2, one_mul]
    _ = -(W * (u - 1)) := by
      rw [key, mul_neg, neg_mul, mul_assoc, mul_assoc, e3, mul_one]

theorem cay_sub_mem_iff {c C : Fin n → Fin n → ℤ} (hc : IsWeight c) (hI : IsIdealWeight c C) {t : L}
    (ht : Valued.v t ≤ 1) {u u' : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (hu' : u' - 1 ∈ upLat L c) :
    -cay t u + cay t u' ∈ upLat L C ↔ u' - u ∈ upLat L C := by
  obtain ⟨z, hz, e1, e2, e⟩ := cay_eq hc ht hu
  obtain ⟨z', hz', e1', e2', e'⟩ := cay_eq hc ht hu'
  rw [← unit_mul_mem_iff hc hI hz hz' (x := u' - u)]
  have hcomm : (1 + z') * (u' - 1) = (u' - 1) * (1 + z') := by
    have : (u' - 1) * (1 + t • (u' - 1)) = (1 + t • (u' - 1)) * (u' - 1) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    calc (1 + z') * (u' - 1) = (1 + z') * ((u' - 1) * (1 + t • (u' - 1))) * (1 + z') := by
          rw [mul_assoc, mul_assoc, e1', mul_one]
      _ = _ := by rw [this, ← mul_assoc, e2', one_mul]
  have key : u' - u = (1 + t • (u - 1)) * (u' - 1) - (u - 1) * (1 + t • (u' - 1)) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  have : (1 + z) * (u' - u) * (1 + z') = -cay t u + cay t u' := by
    rw [key, mul_sub, sub_mul, ← mul_assoc, e2, one_mul, mul_assoc, mul_assoc, e1', mul_one, e, e', hcomm]
    abel
  rw [this]

theorem cay_surj {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) {t : L}
    (ht : Valued.v t ≤ 1) (hσ : t + σ t = 1) {X : Matrix (Fin n) (Fin n) L} (hX : X ∈ upLat L c)
    (hs : X ∈ skewJ σ n) : ∃ u, u - 1 ∈ upLat L c ∧ adjJ σ u * u = 1 ∧ cay t u = X := by
  obtain ⟨z, hz, e1, e2⟩ := exists_inv hc (neg_mem (smul_mem_upLat ht hX))
  rw [mem_skewJ] at hs
  have hst : σ t = 1 - t := by linear_combination hσ
  have e3 := congrArg (adjJ σ) e1
  rw [← sub_eq_add_neg] at e1 e2 e3
  rw [adjJ_mul, adjJ_one, adjJ_sub, adjJ_smul, adjJ_one, hs, smul_neg, sub_neg_eq_add] at e3
  set T := 1 + z with hT
  have h1 : (1 + σ t • X) * T - 1 = X * T := by
    have : (1 + σ t • X) = X + (1 - t • X) := by rw [hst]; module
    rw [this, add_mul, e1, add_sub_cancel_right]
  refine ⟨(1 + σ t • X) * T, ?_, ?_, ?_⟩
  · rw [h1, hT, mul_add, mul_one]
    exact add_mem hX (mul_mem_upLat hc.2 hX hz)
  · rw [adjJ_mul, adjJ_add σ 1 (σ t • X), adjJ_smul, adjJ_one, hs, hσσ, smul_neg, ← sub_eq_add_neg]
    have : (1 - t • X) * (1 + σ t • X) = (1 + σ t • X) * (1 - t • X) := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    rw [mul_assoc, ← mul_assoc (1 - t • X), this, mul_assoc, e1, mul_one, e3]
  · have h2 : 1 + t • (X * T) = T := by
      have := e1
      rw [sub_mul, one_mul, smul_mul_assoc] at this
      rw [← this]; abel
    have h3 : (1 - t • X) * X = X * (1 - t • X) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [cay, h1, h2, Matrix.inv_eq_left_inv e1, ← mul_assoc, h3, mul_assoc, e1, mul_one]

theorem relIndex_unipLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (h : IsUnramInv ϖ σ q) (c C : Fin n → Fin n → ℤ) (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) =
      (upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n) := by
  obtain ⟨⟨t, ht, hσ⟩, -⟩ := exists_trace_one h
  have hadj : ∀ u : (borelU σ n).U, (u.1.1⁻¹).val = adjJ σ u.1.1.val := fun u => (mem_GU_iff_adjJ σ _).1 u.1.2
  have hsk : ∀ u : unipLat h.2.1 hc, cay t u.1.1.1.val ∈ skewJ σ n := fun u =>
    cay_skew hc ht hσ u.2 (by rw [← hadj, Units.mul_inv])
  refine relIndex_eq_of_surj _ _ _ _ (fun u => ⟨cay t u.1.1.1.val, cay_mem hc ht u.2, hsk u⟩) ?_ ?_
  · rintro ⟨X, hX, hs⟩
    obtain ⟨u, hu, e1, e⟩ := cay_surj hc h.1 ht hσ hX hs
    let g : GL (Fin n) L := ⟨u, adjJ σ u, mul_eq_one_comm.1 e1, e1⟩
    have hg : g ∈ GU σ n := (mem_GU_iff_adjJ σ g).2 rfl
    have hU : (⟨g, hg⟩ : GU σ n) ∈ (borelU σ n).U := by
      rw [mem_borelU_U]
      refine ⟨fun i j e => ?_, fun i => ?_⟩
      · have := hu.1 i j (le_of_lt e)
        rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt e), sub_zero] at this
        exact this
      · have := hu.1 i i le_rfl
        rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
        exact this
    exact ⟨⟨⟨⟨g, hg⟩, hU⟩, hu⟩, Subtype.ext e⟩
  · intro u u'
    have h1 : (u.1.1.1⁻¹).val - 1 ∈ upLat L c := (unipLat h.2.1 hc).inv_mem u.2
    have h2 := unit_mul_mem_iff hc hI (x := u'.1.1.1.val - u.1.1.1.val) h1 (zero_mem _)
    rw [add_zero, mul_one, add_sub_cancel, mul_sub, Units.inv_mul] at h2
    show (u.1.1.1⁻¹).val * u'.1.1.1.val - 1 ∈ upLat L C ↔
      -cay t u.1.1.1.val + cay t u'.1.1.1.val ∈ upLat L C ⊓ skewJ σ n
    rw [h2, AddSubgroup.mem_inf, cay_sub_mem_iff hc hI ht u.2 u'.2]
    exact ⟨fun e => ⟨e, add_mem (neg_mem (hsk u)) (hsk u')⟩, fun e => e.1⟩

end GlobalTheory.BorelUMod.Cayley
