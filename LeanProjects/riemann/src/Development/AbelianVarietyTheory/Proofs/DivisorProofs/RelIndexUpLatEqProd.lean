import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ

open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod.UpLatIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ordBall (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (k : ℤ) : AddSubgroup L where
  carrier := {x | (Valued.v x : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-k)}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by simpa using hx

theorem mem_ordBall {k : ℤ} {x : L} : x ∈ ordBall L k ↔ Valued.v x ≤ WithZero.exp (-k) := Iff.rfl

theorem ordBall_mono {k K : ℤ} (h : k ≤ K) : ordBall L K ≤ ordBall L k :=
  fun _ hx => le_trans hx (WithZero.exp_le_exp.2 (neg_le_neg h))

theorem lt_one_iff (a : WithZero (Multiplicative ℤ)) : a < 1 ↔ a ≤ WithZero.exp (-1) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem relIndex_ordBall_succ {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (ordBall L (k + 1)).relIndex (ordBall L k) =
      Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ⧸
        IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hp : ∀ m : ℤ, Valued.v (ϖ ^ m) = WithZero.exp (-m) := fun m => by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  have hle : ∀ (x : L) (a m : ℤ), Valued.v (x * ϖ ^ m) ≤ WithZero.exp (-(a + m)) ↔ Valued.v x ≤ WithZero.exp (-a) :=
    fun x a m => by
      rw [map_mul, hp, neg_add, WithZero.exp_add]
      exact mul_le_mul_iff_left₀ (zero_lt_iff.2 WithZero.exp_ne_zero)
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hm : ∀ x : ordBall L k, x.1 * ϖ ^ (-k) ∈ O := fun x => by
    have := (hle x.1 k (-k)).2 x.2
    rw [add_neg_cancel, neg_zero, WithZero.exp_zero] at this
    exact this
  let g : ordBall L k →+ O :=
    { toFun := fun x => ⟨x.1 * ϖ ^ (-k), hm x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul] }
  let f : ordBall L k →+ O ⧸ IsLocalRing.maximalIdeal O :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).toAddMonoidHom.comp g
  have hf : Function.Surjective f := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y.1 * ϖ ^ k ∈ ordBall L k := by
      have := (hle y.1 0 k).2 (by rw [neg_zero, WithZero.exp_zero]; exact y.2)
      simpa [mem_ordBall] using this
    refine ⟨⟨_, hy⟩, ?_⟩
    change Ideal.Quotient.mk _ (g ⟨_, hy⟩) = _
    congr 1
    ext
    change y.1 * ϖ ^ k * ϖ ^ (-k) = y.1
    rw [mul_assoc, ← zpow_add₀ h0]; simp
  have hc : (ordBall L (k + 1)).addSubgroupOf (ordBall L k) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    change _ ↔ Ideal.Quotient.mk _ (g x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff, lt_one_iff, mem_ordBall,
      ← hle x.1 (k + 1) (-k)]
    have : -(k + 1 + -k) = -1 := by ring
    rw [this]; rfl
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top]

theorem relIndex_ordBall {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {k K : ℤ} (hk : k ≤ K) :
    (ordBall L K).relIndex (ordBall L k) = (q ^ 2) ^ (K - k).toNat := by
  obtain ⟨-, -, -, hϖ, -, -, hq⟩ := h
  obtain ⟨m, rfl⟩ := Int.le.dest hk
  have e : ∀ m : ℕ, (k + m - k).toNat = m := fun m => by omega
  rw [e]
  clear hk
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (ordBall L (k + m + 1)).relIndex (ordBall L (k + m)) = q ^ 2 :=
      (relIndex_ordBall_succ hϖ (k + m)).trans hq
    have h2 := AddSubgroup.relIndex_mul_relIndex (ordBall L (k + m + 1)) (ordBall L (k + m)) (ordBall L k)
      (ordBall_mono (by omega)) (ordBall_mono (by omega))
    rw [Nat.cast_succ, ← add_assoc, ← h2, h1, ih, pow_succ' (q ^ 2)]

theorem relIndex_upLat_eq_prod {n : ℕ} (c C : Fin n → Fin n → ℤ) :
    (upLat L C).relIndex (upLat L c) =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (ordBall L (C p.1.1 p.1.2)).relIndex (ordBall L (c p.1.1 p.1.2)) := by
  let f : upLat L c →+ (∀ p : {p : Fin n × Fin n // p.1 < p.2}, ordBall L (c p.1.1 p.1.2) ⧸
      (ordBall L (C p.1.1 p.1.2)).addSubgroupOf (ordBall L (c p.1.1 p.1.2))) :=
    { toFun := fun x p => QuotientAddGroup.mk ⟨x.1 p.1.1 p.1.2, x.2.2 _ _ p.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i j => if h : i < j then ((y ⟨(i, j), h⟩).out : L) else 0, fun i j h => dif_neg (not_lt.2 h),
      fun i j h => ?_⟩, funext fun p => ?_⟩
    · simp only [dif_pos h]
      exact (y ⟨(i, j), h⟩).out.2
    · refine Eq.trans ?_ (y p).out_eq
      exact congrArg QuotientAddGroup.mk (Subtype.ext (dif_pos p.2))
  have hc : (upLat L C).addSubgroupOf (upLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_upLat]
    constructor
    · intro h p
      exact (QuotientAddGroup.eq_zero_iff _).2 (h.2 _ _ p.2)
    · intro h
      exact ⟨x.2.1, fun i j e => (QuotientAddGroup.eq_zero_iff _).1 (h ⟨(i, j), e⟩)⟩
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem relIndex_upLat : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (q ^ 2) ^ (C p.1 p.2 - c p.1 p.2).toNat := by
  intro L _ _ ϖ σ q n h c C hc
  rw [relIndex_upLat_eq_prod, Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2) _ (by simp)]
  exact Finset.prod_congr rfl fun p _ => relIndex_ordBall h (hc _ _ p.2)

end GlobalTheory.BorelUMod.UpLatIndex
