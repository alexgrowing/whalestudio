import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta Formalism.UG Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.InertCount

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}

theorem col_zero (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : colOf w = 0 := by
  have h1 := ((hH L ϖ σ q N hU).1 w hw).1
  funext i
  have h2 := h1 i.rev
  simp only [h0, Pi.zero_apply, Fin.rev_rev, zero_eq_neg] at h2
  exact (map_eq_zero_iff σ σ.injective).mp h2

theorem mul_row_zero (hH : Heis) (hU : IsUnramInv ϖ σ q) {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N)
    (hw : w ∈ radQ σ N) (h0 : rowOf w = 0) :
    rowOf (u * w) = rowOf u ∧ colOf (u * w) = colOf u ∧ cornerOf (u * w) = cornerOf u + cornerOf w := by
  obtain ⟨hr, hc, hk⟩ := (hH L ϖ σ q N hU).2.1 u hu w hw
  have hcz := col_zero hH hU hw h0
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, h0, add_zero]
  · rw [hc, hcz, add_zero]
  · rw [hk, hcz, dotProduct_zero, add_zero]

theorem trace_corner (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : σ (cornerOf w) + cornerOf w = 0 := by
  have h := ((hH L ϖ σ q N hU).1 w hw).2.1
  rw [h0, zero_dotProduct] at h
  rw [add_comm]
  exact h

theorem small_mul (hH : Heis) (hU : IsUnramInv ϖ σ q) {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hw : w ∈ radQ σ N) (h0 : rowOf w = 0)
    (hs : Small ϖ e f C D u) (hx : ϖ ^ f * cornerOf w ∈ intL L) : Small ϖ e f C D (u * w) := by
  obtain ⟨hr, hc, hk⟩ := mul_row_zero hH hU hu hw h0
  unfold GlobalTheory.InertZeta.Small at hs ⊢
  obtain ⟨hs1, hs2⟩ := hs
  refine ⟨fun j => by rw [hr]; exact hs1 j, ?_⟩
  rw [hr, hc, hk]
  have e : ϖ ^ f * (cornerOf u + cornerOf w - rowOf u ⬝ᵥ D *ᵥ colOf u)
      = ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ D *ᵥ colOf u) + ϖ ^ f * cornerOf w := by ring
  rw [e]
  exact add_mem hs2 hx

theorem corner_of_small (hH : Heis) (hU : IsUnramInv ϖ σ q) {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    {u w : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hw : w ∈ radQ σ N) (h0 : rowOf w = 0)
    (hs : Small ϖ e f C D u) (hs' : Small ϖ e f C D (u * w)) : ϖ ^ f * cornerOf w ∈ intL L := by
  obtain ⟨hr, hc, hk⟩ := mul_row_zero hH hU hu hw h0
  unfold GlobalTheory.InertZeta.Small at hs hs'
  have h2 := hs'.2
  rw [hr, hc, hk] at h2
  have e : ϖ ^ f * cornerOf w = ϖ ^ f * (cornerOf u + cornerOf w - rowOf u ⬝ᵥ D *ᵥ colOf u)
      - ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ D *ᵥ colOf u) := by ring
  rw [e]
  exact sub_mem h2 hs.2

theorem exists_int_lift (hH : Heis) (hU : IsUnramInv ϖ σ q) (ρ : Fin N → L) (hρ : ∀ j, ρ j ∈ intL L) :
    ∃ k ∈ radQ σ N, k ∈ KU σ (N + 2) ∧ rowOf k = ρ := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  have hσσ : ∀ x, σ (σ x) = x := hU.1
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    change Valued.v (σ x) ≤ 1
    rw [hU.2.1]
    exact hx
  have hσs : σ (-∑ j, ρ j * σ (ρ j.rev)) = -∑ j, ρ j * σ (ρ j.rev) := by
    rw [map_neg, map_sum]
    congr 1
    simp only [map_mul, hσσ]
    exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp only [Fin.revPerm_apply, Fin.rev_rev]; ring)
  obtain ⟨u, hu, hrow, hcorner⟩ := (hH L ϖ σ q N hU).2.2 ρ (τ * -∑ j, ρ j * σ (ρ j.rev))
    (by rw [map_mul, hσs, ← add_mul, hτ1, one_mul])
  refine ⟨u, hu, ?_, hrow⟩
  rw [((hH L ϖ σ q N hU).1 u hu).2.2]
  refine ⟨fun j => by rw [hrow]; exact hρ j, ?_⟩
  rw [hcorner]
  exact mul_mem hτ (neg_mem (sum_mem fun j _ => mul_mem (hρ j) (hσint _ (hρ j.rev))))

theorem small_out {e f : ℕ} {C D : Matrix (Fin N) (Fin N) L}
    (hinv : ∀ u ∈ radQ σ N, ∀ k ∈ radQ σ N, k ∈ KU σ (N + 2) → Small ϖ e f C D u → Small ϖ e f C D (u * k))
    (v : radQ σ N) :
    Small ϖ e f C D ((QuotientGroup.mk v : RadQuot σ N).out : radQ σ N).1 ↔ Small ϖ e f C D v.1 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) v
  rw [hh]
  have hk : ((h : radQ σ N) : GU σ (N + 2)) ∈ KU σ (N + 2) := Subgroup.mem_subgroupOf.mp h.2
  have hkr : ((h : radQ σ N) : GU σ (N + 2)) ∈ radQ σ N := (h : radQ σ N).2
  constructor
  · intro hs
    have h2 := hinv _ (v * h).2 _ (inv_mem hkr) (inv_mem hk) hs
    simpa using h2
  · intro hs
    exact hinv _ v.2 _ hkr hk hs

theorem vecMul_smul_apply (c : L) (r : Fin N → L) (C : Matrix (Fin N) (Fin N) L) (j : Fin N) :
    (r ᵥ* (c • C)) j = c * (r ᵥ* C) j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isInt_smul {ϖ : L} (hϖ : ϖ ∈ intL L) (e : ℕ) {C : Matrix (Fin N) (Fin N) L} (hC : IsInt C) :
    IsInt (ϖ ^ e • C) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (pow_mem hϖ e) (hC i j)

theorem v_det_smul {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (e l : ℕ) {C : Matrix (Fin N) (Fin N) L}
    (hdet : Valued.v C.det = WithZero.exp (-(l : ℤ))) :
    Valued.v (ϖ ^ e • C).det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, map_pow, hϖ, hdet, ← pow_mul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem eq_of_neg_add_out {G : Type*} [AddGroup G] {S : AddSubgroup G} (y y' : G ⧸ S)
    (h : -y.out + y'.out ∈ S) : y = y' := by
  calc y = QuotientAddGroup.mk y.out := (QuotientAddGroup.out_eq' y).symm
    _ = QuotientAddGroup.mk y'.out := QuotientAddGroup.eq.mpr h
    _ = y' := QuotientAddGroup.out_eq' y'

theorem neg_add_out_mem {G : Type*} [AddGroup G] {S : AddSubgroup G} (a : G) :
    -a + (QuotientAddGroup.mk a : G ⧸ S).out ∈ S := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : G ⧸ S)).symm

private theorem inv_lemma' (hH : Heis) (hU : IsUnramInv ϖ σ q) {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ (rowOf u = 0 → cornerOf u⁻¹ = -cornerOf u) := by
  obtain ⟨hr1, -, hk1⟩ := (hH L ϖ σ q N hU).2.1 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at hr1 hk1
  have hrow1 : rowOf (1 : GU σ (N + 2)) = 0 := by
    have e : rowOf (1 : GU σ (N + 2)) + rowOf (1 : GU σ (N + 2)) = rowOf (1 : GU σ (N + 2)) + 0 := by rw [add_zero]; exact hr1.symm
    exact add_left_cancel e
  have hcor1 : cornerOf (1 : GU σ (N + 2)) = 0 := by
    rw [hrow1, zero_dotProduct, add_zero] at hk1
    have e : cornerOf (1 : GU σ (N + 2)) + cornerOf (1 : GU σ (N + 2)) = cornerOf (1 : GU σ (N + 2)) + 0 := by rw [add_zero]; exact hk1.symm
    exact add_left_cancel e
  obtain ⟨hr, -, hk⟩ := (hH L ϖ σ q N hU).2.1 u hu u⁻¹ (inv_mem hu)
  rw [mul_inv_cancel, hrow1] at hr
  rw [mul_inv_cancel, hcor1] at hk
  refine ⟨?_, fun h0 => ?_⟩
  · calc rowOf u⁻¹ = (rowOf u + rowOf u⁻¹) - rowOf u := by abel
      _ = -rowOf u := by rw [← hr]; abel
  · rw [h0, zero_dotProduct, add_zero] at hk
    calc cornerOf u⁻¹ = (cornerOf u + cornerOf u⁻¹) - cornerOf u := by abel
      _ = -cornerOf u := by rw [← hk]; abel

theorem count (hH : Heis) (hL : LatIndex) (hT : TraceIndex) : Count := by
  unfold GlobalTheory.InertZeta.Count
  intro L _ _ ϖ σ q N hU C D l e f hC hdet hsurj hinv
  have hϖv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hϖ : ϖ ∈ intL L := by
    change Valued.v ϖ ≤ 1
    rw [hϖv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hrowS : ∀ u : GU σ (N + 2), Small ϖ e f C D u → rowOf u ∈ preLat (ϖ ^ e • C) := fun u hs => by
    unfold GlobalTheory.InertZeta.Small at hs
    exact mem_preLat.mpr fun j => by rw [vecMul_smul_apply]; exact hs.1 j
  have hub : ∀ b : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))), ∃ u ∈ radQ σ N,
      rowOf u = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) ∧ Small ϖ e f C D u :=
    fun b => hsurj _ (fun j => by
      have h1 := (mem_preLat.mp (Quotient.out b : preLat (ϖ ^ e • C)).2) j
      rwa [vecMul_smul_apply] at h1)
  choose ub hubR hubrow hubS using hub
  have hwt : ∀ t : (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))), ∃ w ∈ radQ σ N,
      rowOf w = 0 ∧ cornerOf w = ((Quotient.out t : traceZero σ (ϖ ^ f)) : L) :=
    fun t => (hH L ϖ σ q N hU).2.2 0 _ (by
      have h1 := (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).2
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]
      rw [add_comm]
      exact h1)
  choose wt hwtR hwtrow hwtcorner using hwt
  have hwtint : ∀ t, ϖ ^ f * cornerOf (wt t) ∈ intL L := fun t => by
    rw [hwtcorner]
    exact (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).1
  have key_row : ∀ b t, rowOf (ub b * wt t) = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) :=
    fun b t => by
      rw [((hH L ϖ σ q N hU).2.1 _ (hubR b) _ (hwtR t)).1, hwtrow, add_zero, hubrow]
  let G : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) × (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))) → {x : RadQuot σ N // Small ϖ e f C D (Quotient.out x : radQ σ N).1} :=
    fun p => ⟨QuotientGroup.mk (⟨ub p.1 * wt p.2, mul_mem (hubR p.1) (hwtR p.2)⟩ : radQ σ N),
      (small_out hinv _).mpr
        (small_mul hH hU (hubR p.1) (hwtR p.2) (hwtrow p.2) (hubS p.1) (hwtint p.2))⟩
  have hinj : Function.Injective G := by
    rintro ⟨b, t⟩ ⟨b', t'⟩ hGG
    have h1 : (QuotientGroup.mk (⟨ub b * wt t, mul_mem (hubR b) (hwtR t)⟩ : radQ σ N) : RadQuot σ N)
        = QuotientGroup.mk (⟨ub b' * wt t', mul_mem (hubR b') (hwtR t')⟩ : radQ σ N) :=
      congrArg Subtype.val hGG
    have hz : (ub b * wt t)⁻¹ * (ub b' * wt t') ∈ KU σ (N + 2) :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
    have hzR : (ub b * wt t)⁻¹ * (ub b' * wt t') ∈ radQ σ N :=
      mul_mem (inv_mem (mul_mem (hubR b) (hwtR t))) (mul_mem (hubR b') (hwtR t'))
    obtain ⟨hzrow, hzcorner⟩ := (((hH L ϖ σ q N hU).1 _ hzR).2.2).mp hz
    have hrowz : rowOf ((ub b * wt t)⁻¹ * (ub b' * wt t'))
        = -((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L)
          + ((Quotient.out b' : preLat (ϖ ^ e • C)) : Fin N → L) := by
      rw [((hH L ϖ σ q N hU).2.1 _ (inv_mem (mul_mem (hubR b) (hwtR t))) _
        (mul_mem (hubR b') (hwtR t'))).1, (inv_lemma' hH hU (mul_mem (hubR b) (hwtR t))).1, key_row, key_row]
    have hbb : b = b' := eq_of_neg_add_out b b' (by
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV]
      intro i
      have h2 := hzrow i
      rw [hrowz] at h2
      simpa using h2)
    subst hbb
    have hz' : (ub b * wt t)⁻¹ * (ub b * wt t') = (wt t)⁻¹ * wt t' := by group
    rw [hz'] at hzcorner
    obtain ⟨-, -, hk⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ (hwtR t')
    rw [hk, (inv_lemma' hH hU (hwtR t)).2 (hwtrow t), (inv_lemma' hH hU (hwtR t)).1, hwtrow, neg_zero,
      zero_dotProduct, add_zero, hwtcorner, hwtcorner] at hzcorner
    have htt : t = t' := eq_of_neg_add_out t t' (by
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero]
      refine ⟨by simpa using hzcorner, ?_⟩
      have h1 := (mem_traceZero.mp (Quotient.out t : traceZero σ (ϖ ^ f)).2).2
      have h2 := (mem_traceZero.mp (Quotient.out t' : traceZero σ (ϖ ^ f)).2).2
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, map_add, map_neg]
      linear_combination -h1 + h2)
    rw [htt]
  have hsurjG : Function.Surjective G := by
    rintro ⟨x, hx⟩
    have hxv : (QuotientGroup.mk (Quotient.out x) : RadQuot σ N) = x := QuotientGroup.out_eq' x
    have hvS : Small ϖ e f C D (Quotient.out x : radQ σ N).1 := hx
    have hvrow := hrowS _ hvS
    obtain ⟨b, hb⟩ : ∃ b : (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))),
        b = QuotientAddGroup.mk (⟨rowOf (Quotient.out x : radQ σ N).1, hvrow⟩ : preLat (ϖ ^ e • C)) := ⟨_, rfl⟩
    have hρ := neg_add_out_mem (S := (intV L N).addSubgroupOf (preLat (ϖ ^ e • C)))
      (⟨rowOf (Quotient.out x : radQ σ N).1, hvrow⟩ : preLat (ϖ ^ e • C))
    rw [← hb, AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
    obtain ⟨k, hkR, hkK, hkrow⟩ := exists_int_lift hH hU
      (fun i => -rowOf (Quotient.out x : radQ σ N).1 i + ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) i)
      (fun i => by simpa using hρ i)
    have hv'row : rowOf ((Quotient.out x : radQ σ N).1 * k) = ((Quotient.out b : preLat (ϖ ^ e • C)) : Fin N → L) := by
      rw [((hH L ϖ σ q N hU).2.1 _ (Quotient.out x).2 _ hkR).1, hkrow]
      funext i
      simp
    have hv'S : Small ϖ e f C D ((Quotient.out x : radQ σ N).1 * k) := hinv _ (Quotient.out x).2 _ hkR hkK hvS
    have hwR : ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) ∈ radQ σ N := mul_mem (inv_mem (hubR b)) (mul_mem (Quotient.out x).2 hkR)
    have hw0 : rowOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) = 0 := by
      rw [((hH L ϖ σ q N hU).2.1 _ (inv_mem (hubR b)) _ (mul_mem (Quotient.out x).2 hkR)).1,
        (inv_lemma' hH hU (hubR b)).1, hubrow, hv'row, neg_add_cancel]
    have hmul : ub b * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) = (Quotient.out x : radQ σ N).1 * k := by group
    have hcw := corner_of_small hH hU (hubR b) hwR hw0 (hubS b) (by rw [hmul]; exact hv'S)
    have htr := trace_corner hH hU hwR hw0
    obtain ⟨t, ht⟩ : ∃ t : (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))),
        t = QuotientAddGroup.mk (⟨cornerOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)), mem_traceZero.mpr ⟨hcw, htr⟩⟩ : traceZero σ (ϖ ^ f)) :=
      ⟨_, rfl⟩
    refine ⟨(b, t), Subtype.ext ?_⟩
    show (QuotientGroup.mk (⟨ub b * wt t, mul_mem (hubR b) (hwtR t)⟩ : radQ σ N) : RadQuot σ N) = x
    rw [← hxv]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show (ub b * wt t)⁻¹ * (Quotient.out x : radQ σ N).1 ∈ KU σ (N + 2)
    have hy : (ub b * wt t)⁻¹ * (Quotient.out x : radQ σ N).1 = ((wt t)⁻¹ * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k))) * k⁻¹ := by group
    rw [hy]
    refine mul_mem ?_ (inv_mem hkK)
    have hRR : (wt t)⁻¹ * ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)) ∈ radQ σ N := mul_mem (inv_mem (hwtR t)) hwR
    refine (((hH L ϖ σ q N hU).1 _ hRR).2.2).mpr ⟨fun j => ?_, ?_⟩
    · obtain ⟨hr, -, -⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ hwR
      rw [hr, (inv_lemma' hH hU (hwtR t)).1, hwtrow, hw0]
      simp
    · obtain ⟨-, -, hk⟩ := (hH L ϖ σ q N hU).2.1 _ (inv_mem (hwtR t)) _ hwR
      rw [hk, (inv_lemma' hH hU (hwtR t)).2 (hwtrow t), (inv_lemma' hH hU (hwtR t)).1, hwtrow, neg_zero,
        zero_dotProduct, add_zero, hwtcorner]
      have hm := neg_add_out_mem (S := (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f)))
        (⟨cornerOf ((ub b)⁻¹ * ((Quotient.out x : radQ σ N).1 * k)), mem_traceZero.mpr ⟨hcw, htr⟩⟩ : traceZero σ (ϖ ^ f))
      rw [← ht, AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hm
      simpa using neg_mem hm.1
  have hbij : Function.Bijective G := ⟨hinj, hsurjG⟩
  have h1 := hL L ϖ σ q N hU (ϖ ^ e • C) (l + N * e) (isInt_smul hϖ e hC) (v_det_smul hϖv e l hdet)
  have h2 := hT L ϖ σ q f hU
  calc Nat.card {x : RadQuot σ N // Small ϖ e f C D (Quotient.out x : radQ σ N).1}
        = Nat.card ((↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) × (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f)))) := (Nat.card_congr (Equiv.ofBijective G hbij)).symm
    _ = Nat.card (↥(preLat (ϖ ^ e • C)) ⧸ (intV L N).addSubgroupOf (preLat (ϖ ^ e • C))) * Nat.card (↥(traceZero σ (ϖ ^ f)) ⧸ (traceZero σ 1).addSubgroupOf (traceZero σ (ϖ ^ f))) := Nat.card_prod _ _
    _ = (intV L N).relIndex (preLat (ϖ ^ e • C)) * (traceZero σ 1).relIndex (traceZero σ (ϖ ^ f)) := rfl
    _ = q ^ (2 * (l + N * e) + f) := by rw [h1, h2, pow_add]

end GlobalTheory.CompanionTheory.InertCount

end
