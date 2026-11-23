import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section HeisCalc

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rowOf_one : rowOf (1 : GU σ (N + 2)) = 0 := funext fun j =>
  Matrix.one_apply_ne (mid_ne_zero j).symm

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem colOf_one : colOf (1 : GU σ (N + 2)) = 0 := funext fun i =>
  Matrix.one_apply_ne (mid_ne_last i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cornerOf_one : cornerOf (1 : GU σ (N + 2)) = 0 :=
  Matrix.one_apply_ne (last_ne_zero (N := N)).symm

variable
  (h1 : ∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧ cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L))
  (h2 : ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u')
include h1

theorem colOf_eq_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : colOf u = colOf u' := funext fun i => by
  have a := (h1 u hu).1 i.rev
  have b := (h1 u' hu').1 i.rev
  rw [Fin.rev_rev, h] at a
  rw [Fin.rev_rev] at b
  exact σ.injective (neg_injective (a.symm.trans b))

theorem colOf_eq_zero {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (h : rowOf u = 0) : colOf u = 0 := by
  rw [colOf_eq_of_rowOf_eq h1 hu (one_mem _) (h.trans rowOf_one.symm), colOf_one]

include h2

theorem rowOf_inv {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ cornerOf u⁻¹ = -cornerOf u + rowOf u ⬝ᵥ colOf u := by
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u hu
  rw [inv_mul_cancel, rowOf_one] at r
  rw [inv_mul_cancel, cornerOf_one] at c
  have r' : rowOf u⁻¹ = -rowOf u := eq_neg_of_add_eq_zero_left r.symm
  refine ⟨r', ?_⟩
  rw [r', neg_dotProduct] at c
  linear_combination -c

theorem inv_mul_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : rowOf (u⁻¹ * u') = 0 ∧ cornerOf (u⁻¹ * u') = cornerOf u' - cornerOf u := by
  obtain ⟨ri, ci⟩ := rowOf_inv h1 h2 hu
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u' hu'
  have hc := colOf_eq_of_rowOf_eq h1 hu hu' h
  refine ⟨by rw [r, ri, h, neg_add_cancel], ?_⟩
  rw [c, ci, ri, ← hc, neg_dotProduct]
  ring

theorem rowOf_inv_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u⁻¹ * u') = -rowOf u + rowOf u' := by
  rw [(h2 u⁻¹ (inv_mem hu) u' hu').1, (rowOf_inv h1 h2 hu).1]

theorem mul_of_rowOf_eq_zero {u z : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hz : z ∈ radQ σ N) (h : rowOf z = 0) :
    rowOf (u * z) = rowOf u ∧ colOf (u * z) = colOf u ∧ cornerOf (u * z) = cornerOf u + cornerOf z := by
  obtain ⟨r, b, c⟩ := h2 u hu z hz
  have hb := colOf_eq_zero h1 hz h
  refine ⟨by rw [r, h, add_zero], by rw [b, hb, add_zero], by rw [c, hb, dotProduct_zero, add_zero]⟩

end HeisCalc

end GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta

theorem count_of_heis : Heis → LatIndex → TraceIndex → Count := by
  intro hH hL hT L _ _ ϖ σ q N hU C D l e f hC hdet hex hinv
  obtain ⟨h1, h2, h3⟩ := hH L ϖ σ q N hU
  have hσσ := hU.1
  have hσv := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := hU.2.2.2.1
  have hϖ1 : ϖ ∈ intL L := by show Valued.v ϖ ≤ 1; rw [hϖ]; exact oneLePart_eq_one.mp rfl
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx

  set A : Matrix (Fin N) (Fin N) L := ϖ ^ e • C with hA
  have hAint : IsInt A := fun i j => by
    rw [hA, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (pow_mem hϖ1 _) (hC i j)
  have hAdet : Valued.v A.det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
    rw [hA, Matrix.det_smul, map_mul, map_pow, map_pow, hϖ, hdet, Fintype.card_fin, ← WithZero.exp_nsmul,
      ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1; push_cast; ring
  have iL := hL L ϖ σ q N hU A (l + N * e) hAint hAdet
  have iT := hT L ϖ σ q f hU
  set Λ := preLat A
  set I := intV L N
  set T := traceZero σ (ϖ ^ f)
  set T₀ := traceZero σ 1
  have memΛ : ∀ r : Fin N → L, r ∈ Λ ↔ ∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L := fun r => by
    rw [mem_preLat, hA, Matrix.vecMul_smul]; rfl
  rw [pow_add, ← iL, ← iT]

  have ex0 : ∀ r : Λ, ∃ u : radQ σ N, rowOf (u : GU σ (N + 2)) = r ∧ Small ϖ e f C D (u : GU σ (N + 2)) := fun r => by
    obtain ⟨u, hu, h, hs⟩ := hex r ((memΛ r).1 r.2)
    exact ⟨⟨u, hu⟩, h, hs⟩
  choose u₀ hu₀r hu₀s using ex0
  have exz : ∀ t : T, ∃ z : radQ σ N, rowOf (z : GU σ (N + 2)) = 0 ∧ cornerOf (z : GU σ (N + 2)) = t := fun t => by
    have ht := (mem_traceZero.1 t.2).2
    obtain ⟨z, hz, h, hc⟩ := h3 0 t (by
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]; linear_combination ht)
    exact ⟨⟨z, hz⟩, h, hc⟩
  choose z hzr hzc using exz
  have smallOut : ∀ w : radQ σ N, Small ϖ e f C D (w : GU σ (N + 2)) →
      Small ϖ e f C D (((QuotientGroup.mk w : RadQuot σ N).out : radQ σ N) : GU σ (N + 2)) := fun w hw => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) w
    rw [hk]
    exact hinv w.1 w.2 k.1.1 k.1.2 (Subgroup.mem_subgroupOf.1 k.2) hw
  have smallW : ∀ (r : Λ) (t : T), Small ϖ e f C D ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) := fun r t => by
    obtain ⟨hr, hb, hc⟩ := mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)
    have hs := hu₀s r
    show Small ϖ e f C D ((u₀ r : GU σ (N + 2)) * (z t : GU σ (N + 2)))
    refine ⟨fun j => ?_, ?_⟩
    · rw [hr]; exact hs.1 j
    · rw [hr, hb, hc, hzc]
      convert add_mem hs.2 (mem_traceZero.1 t.2).1 using 1
      ring
  have rowW : ∀ (r : Λ) (t : T), rowOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) = r := fun r t =>
    ((mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).1).trans (hu₀r r)
  have cornerW : ∀ (r : Λ) (t : T), cornerOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) =
      cornerOf (u₀ r : GU σ (N + 2)) + t := fun r t => by
    rw [← hzc t]; exact (mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).2.2
  let Φ : (Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T) →
      {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} := fun p =>
    ⟨QuotientGroup.mk (u₀ p.1.out * z p.2.out), smallOut _ (smallW _ _)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have hk := QuotientGroup.eq.1 (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf] at hk
      have hK := (h1 _ ((u₀ a.out * z b.out)⁻¹ * (u₀ a'.out * z b'.out)).2).2.2.1 hk
      have ha : a = a' := by
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' a', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_intV]
        intro j
        have := hK.1 j
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, rowOf_inv_mul h1 h2 (u₀ a.out * z b.out).2 (u₀ a'.out * z b'.out).2,
          rowW, rowW] at this
      subst ha
      have hb : b = b' := by
        rw [← QuotientAddGroup.out_eq' b, ← QuotientAddGroup.out_eq' b', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_traceZero]
        have hd := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out * z b.out).2 (u₀ a.out * z b'.out).2
          ((rowW _ _).trans (rowW _ _).symm)
        have hc := hK.2
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hd.2, cornerW, cornerW] at hc
        have t1 := (mem_traceZero.1 b.out.2).2
        have t2 := (mem_traceZero.1 b'.out.2).2
        refine ⟨?_, ?_⟩
        · convert hc using 1; push_cast; ring
        · push_cast; rw [map_add, map_neg]; linear_combination t2 - t1
      rw [hb]
    · rintro ⟨x, hx⟩

      have hrΛ : rowOf ((x.out : radQ σ N) : GU σ (N + 2)) ∈ Λ := (memΛ _).2 hx.1
      have hρ : (-(⟨_, hrΛ⟩ : Λ) + (QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) : Λ ⧸ I.addSubgroupOf Λ).out) ∈
          I.addSubgroupOf Λ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
      set a : Λ ⧸ I.addSubgroupOf Λ := QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) with ha
      set u : radQ σ N := x.out with hu
      set ρ : Fin N → L := -rowOf (u : GU σ (N + 2)) + (a.out : Fin N → L) with hρdef
      have hρ' : ∀ i, ρ i ∈ intL L := hρ
      obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
      set s : L := -∑ j, ρ j * σ (ρ j.rev) with hsdef
      have hs : σ s = s := by
        simp only [hsdef, map_neg, map_sum, map_mul, hσσ]
        congr 1
        exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [mul_comm])
      have hsint : s ∈ intL L := neg_mem (Subring.sum_mem _ fun j _ => mul_mem (hρ' j) (hσint _ (hρ' _)))
      obtain ⟨k, hk, hkr, hkc⟩ := h3 ρ (τ * s) (by rw [map_mul, hs]; linear_combination s * hτ1)
      have hkK : k ∈ KU σ (N + 2) := (h1 k hk).2.2.2 ⟨fun j => hkr ▸ hρ' j, hkc ▸ mul_mem hτ hsint⟩
      set uk : radQ σ N := u * ⟨k, hk⟩ with hukdef
      have hukS : Small ϖ e f C D (uk : GU σ (N + 2)) := hinv u.1 u.2 k hk hkK hx
      have hukr : rowOf (uk : GU σ (N + 2)) = a.out := by
        rw [hukdef, Subgroup.coe_mul, (h2 _ u.2 _ hk).1, hkr, hρdef, add_neg_cancel_left]
      have hv := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
      set v : radQ σ N := (u₀ a.out)⁻¹ * uk with hvdef
      have hvr : rowOf (v : GU σ (N + 2)) = 0 := hv.1
      have hvc : cornerOf (v : GU σ (N + 2)) = cornerOf (uk : GU σ (N + 2)) - cornerOf (u₀ a.out : GU σ (N + 2)) := hv.2
      have htT : cornerOf (v : GU σ (N + 2)) ∈ T := by
        rw [mem_traceZero]
        refine ⟨?_, ?_⟩
        · have hcol := colOf_eq_of_rowOf_eq h1 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
          have := sub_mem hukS.2 (hu₀s a.out).2
          rw [hukr, ← hcol, hu₀r] at this
          rw [hvc]
          convert this using 1
          ring
        · have := (h1 _ v.2).2.1
          rw [hvr, zero_dotProduct] at this
          linear_combination this
      set bq : T ⧸ T₀.addSubgroupOf T := QuotientAddGroup.mk (⟨_, htT⟩ : T) with hbq
      have hδ : (-(⟨_, htT⟩ : T) + bq.out) ∈ T₀.addSubgroupOf T := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hδ
      refine ⟨(a, bq), Subtype.ext ?_⟩
      show (QuotientGroup.mk (u₀ a.out * z bq.out) : RadQuot σ N) = x
      have e1 : (QuotientGroup.mk u : RadQuot σ N) = QuotientGroup.mk uk :=
        QuotientGroup.eq.2 (by rw [hukdef, inv_mul_cancel_left]; exact Subgroup.mem_subgroupOf.2 hkK)
      rw [← QuotientGroup.out_eq' x, ← hu, e1, QuotientGroup.eq,
        show (u₀ a.out * z bq.out)⁻¹ * uk = (z bq.out)⁻¹ * v by rw [hvdef, _root_.mul_inv_rev, mul_assoc],
        Subgroup.mem_subgroupOf]
      have hzv := inv_mul_of_rowOf_eq h1 h2 (z bq.out).2 v.2 ((hzr _).trans hvr.symm)
      refine (h1 _ ((z bq.out)⁻¹ * v).2).2.2.2 ⟨fun j => ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.1]; exact zero_mem _
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.2, hzc]
        have := neg_mem hδ.1
        convert this using 1
        push_cast
        ring
  rw [show I.relIndex Λ * T₀.relIndex T = Nat.card ((Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T)) from
    (Nat.card_prod _ _).symm]
  exact (Nat.card_eq_of_bijective Φ hΦ).symm

end GlobalTheory.InertZeta
