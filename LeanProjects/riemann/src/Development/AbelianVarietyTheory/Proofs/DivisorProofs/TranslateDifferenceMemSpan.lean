import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD

noncomputable section

open ValuativeRel

namespace GlobalTheory.PrinTwo.DiffTr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_le (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx hy ⊢
  have h := (valuation k).map_add (y - x) x
  rw [sub_add_cancel] at h
  exact h.trans (max_le hy.le hx)

def ballSub (r : kˣ) : AddSubgroup k where
  carrier := {z | valuation k z ≤ valuation k (r : k)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    show valuation k (a + b) ≤ valuation k (r : k) from (valuation k).map_add_le ha hb
  neg_mem' := fun {a} ha =>
    show valuation k (-a) ≤ valuation k (r : k) by rw [Valuation.map_neg]; exact ha

theorem mem_ballSub (r : kˣ) (z : k) : z ∈ ballSub r ↔ valuation k z ≤ valuation k (r : k) :=
  Iff.rfl

theorem mem_ball_iff (r : kˣ) (x c : k) :
    x ∈ ball c r ↔ (QuotientAddGroup.mk x : k ⧸ ballSub r) = QuotientAddGroup.mk c := by
  rw [QuotientAddGroup.eq, mem_ballSub]
  show valuation k (x - c) ≤ valuation k (r : k) ↔ valuation k (-x + c) ≤ valuation k (r : k)
  rw [show -x + c = -(x - c) by ring, Valuation.map_neg]

theorem apply_out (r : kˣ) (Φ : k → ℂ)
    (hr : ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x) (x : k) :
    Φ (Quotient.out (QuotientAddGroup.mk x : k ⧸ ballSub r)) = Φ x := by
  have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk x : k ⧸ ballSub r)) :
      k ⧸ ballSub r) = QuotientAddGroup.mk x := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq, mem_ballSub] at h1
  have h4 := hr (Quotient.out (QuotientAddGroup.mk x : k ⧸ ballSub r)) _ h1
  rw [← h4]; congr 1; ring

theorem finite_image (r : kˣ) (γ : ValueGroupWithZero k) :
    ((QuotientAddGroup.mk : k → k ⧸ ballSub r) '' {x | valuation k x ≤ γ}).Finite := by
  have hcov : {x : k | valuation k x ≤ γ} ⊆
      ⋃ c ∈ {x : k | valuation k x ≤ γ}, ball c r := by
    intro x hx
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, by simp [ball]⟩
  have hopen : ∀ c ∈ {x : k | valuation k x ≤ γ}, IsOpen (ball c r) := by
    intro c _
    have h0 : valuation k (r : k) ≠ 0 := by simp
    exact (isOpen_le _ h0).preimage (continuous_sub_right c)
  obtain ⟨t, -, ht, hBt⟩ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall k γ).elim_finite_subcover_image hopen hcov
  refine (ht.image (QuotientAddGroup.mk : k → k ⧸ ballSub r)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  have := hBt hx
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hxc⟩ := this
  exact ⟨c, hc, ((mem_ball_iff r x c).1 hxc).symm⟩

end GlobalTheory.PrinTwo.DiffTr

namespace GlobalTheory.PrinTwo.DiffTr
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diff_mem (Φ : k → ℂ) (hΦ : IsLC Φ) (hR : IsEvRad Φ) (y : k) :
    (fun x => Φ (x + y) - Φ x) ∈ elemSpan k := by
  classical
  obtain ⟨r, hr⟩ := hΦ
  obtain ⟨R, hRad⟩ := hR
  let mk : k → k ⧸ ballSub r := QuotientAddGroup.mk
  let f : k ⧸ ballSub r → ℂ := fun q => Φ (Quotient.out q)
  have hf : ∀ x, f (mk x) = Φ x := apply_out r Φ hr
  have hmk : ∀ a b : k, mk (a + b) = mk a + mk b := fun a b => rfl
  have hmks : ∀ a b : k, mk (a - b) = mk a - mk b := fun a b => rfl
  have hout' : ∀ q : k ⧸ ballSub r, mk (Quotient.out q) = q := fun q => QuotientAddGroup.out_eq' q
  obtain ⟨γ, hRγ, hy⟩ : ∃ γ : ValueGroupWithZero k, valuation k (R : k) ≤ γ ∧ valuation k y ≤ γ :=
    ⟨max (valuation k (R : k)) (valuation k y), le_max_left _ _, le_max_right _ _⟩
  have hfin := finite_image r γ
  let S := hfin.toFinset
  have hmemS : ∀ q, q ∈ S ↔ ∃ x, valuation k x ≤ γ ∧ mk x = q := by
    intro q; simp [S, mk]
  have hBy : ∀ x, valuation k x ≤ γ → valuation k (x + y) ≤ γ :=
    fun x hx => (valuation k).map_add_le hx hy
  have hBy' : ∀ x, valuation k x ≤ γ → valuation k (x - y) ≤ γ := fun x hx =>
    (valuation k).map_add_le hx (show valuation k (-y) ≤ γ by rwa [Valuation.map_neg])
      |>.trans_eq' (by rw [sub_eq_add_neg])
  have hS : ∀ q, q + mk y ∈ S ↔ q ∈ S := by
    intro q
    rw [hmemS, hmemS]
    constructor
    · rintro ⟨x, hx, hxq⟩
      refine ⟨x - y, hBy' x hx, ?_⟩
      rw [hmks, hxq]; abel
    · rintro ⟨x, hx, rfl⟩; exact ⟨x + y, hBy x hx, hmk x y⟩
  have hsum : ∑ q ∈ S, (f (q + mk y) - f q) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Finset.sum_nbij' (fun q => q + mk y) (fun q => q - mk y)
      (fun q hq => (hS q).2 hq) (fun q hq => (hS (q - mk y)).1 (by simpa using hq))
      (fun q _ => by simp) (fun q _ => by simp) (fun q _ => rfl)
  have hvanish : ∀ x, ¬ valuation k x ≤ γ → Φ (x + y) - Φ x = 0 := by
    intro x hx
    rw [not_le] at hx
    have hxy : valuation k (x + y) = valuation k x := by
      rw [add_comm]; exact Valuation.map_add_eq_of_lt_right _ (lt_of_le_of_lt hy hx)
    rw [sub_eq_zero]
    exact (hRad x (x + y) (lt_of_le_of_lt hRγ hx) hxy.symm).symm
  have heq : (fun x => Φ (x + y) - Φ x) =
      ∑ q ∈ S, (f (q + mk y) - f q) • elemDiff (Quotient.out q) (Quotient.out (0 : k ⧸ ballSub r)) r := by
    funext x
    rw [Finset.sum_apply]
    have hind : ∀ c : k, (ball c r).indicator (1 : k → ℂ) x = if mk x = mk c then 1 else 0 := by
      intro c
      rw [Set.indicator_apply]
      simp only [mem_ball_iff, Pi.one_apply]
      rfl
    simp only [Pi.smul_apply, elemDiff, Pi.sub_apply, hind, hout', smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    have hval : f (mk x + mk y) - f (mk x) = Φ (x + y) - Φ x := by
      rw [← hmk, hf, hf]
    split_ifs with hxS
    · exact hval.symm
    · have hxB : ¬ valuation k x ≤ γ := fun hB => hxS ((hmemS _).2 ⟨x, hB, rfl⟩)
      exact hvanish x hxB
  rw [heq]
  refine Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨(Quotient.out q, Quotient.out (0 : k ⧸ ballSub r), r), rfl⟩

theorem diff_mem_elemSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Φ : k → ℂ), GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsEvRad Φ →
    ∀ y : k, (fun x => Φ (x + y) - Φ x) ∈ GlobalTheory.PrinTwo.elemSpan k :=
  fun _ _ _ _ _ Φ hΦ hR y => diff_mem Φ hΦ hR y

end GlobalTheory.PrinTwo.DiffTr
