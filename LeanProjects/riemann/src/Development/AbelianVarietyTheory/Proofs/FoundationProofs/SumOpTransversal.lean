import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial

noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

section
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem quot_mk_eq_iff (A B : Submodule R X) (x y : B.toAddSubgroup) :
    (QuotientAddGroup.mk x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = QuotientAddGroup.mk y ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : ((-x + y : B.toAddSubgroup) : X) = (y : X) - x := by
    push_cast; abel
  rw [this]; rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_mk_eq_mk_iff_sub_mem (A B : Submodule R X) (x y : B.toAddSubgroup) :
    ((x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = y) ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  simp [neg_add_eq_sub]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma heis_apply_eq_of_sub_mem_of_fixes {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : y - x ∈ A) : W y v = W x v := by
  have hyx : y - x ∈ B := B.sub_mem hy hx
  calc W y v = W (x + (y - x)) v := by rw [add_sub_cancel]
    _ = W x (W (y - x) v) := (h.comp_of_mem hB hx hyx v).symm
    _ = W x v := by rw [hv _ hxy]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma quotient_out_sub_mem (A B : Submodule R X)
    (q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) (x : B.toAddSubgroup)
    (hq : (x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = q) :
    ((Quotient.out q : B.toAddSubgroup) : X) - x ∈ A := by
  rw [← quotient_mk_eq_mk_iff_sub_mem, hq]
  exact (QuotientAddGroup.out_eq' q).symm

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (A B : Submodule R X) (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) (v : M)
    (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) (ι : Type) [Fintype ι] (f : ι → X)
    (hf : ∀ i, f i ∈ B) (ht : ∀ b ∈ B, ∃! i, b - f i ∈ A) :
    _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
      _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι := by
  let φ : ι → B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    fun i => ((⟨f i, hf i⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hφ : Function.Bijective φ := by
    constructor
    · intro i j hij
      have hji : f j - f i ∈ A := (quotient_mk_eq_mk_iff_sub_mem A B _ _).1 hij
      obtain ⟨k, -, hk⟩ := ht (f j) (hf j)
      rw [hk i hji, hk j (by simp)]
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H b =>
        obtain ⟨i, hi, -⟩ := ht b b.2
        exact ⟨i, (quotient_mk_eq_mk_iff_sub_mem A B _ _).2 hi⟩
  let e := Equiv.ofBijective φ hφ
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact heis_apply_eq_of_sub_mem_of_fixes h hB hv (hf i) (Quotient.out (e i)).2
      (quotient_out_sub_mem A B (e i) ⟨f i, hf i⟩ rfl)
  · unfold _root_.GlobalTheory.FinWeil.idx
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr e, Nat.card_eq_fintype_card]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero (A B : Submodule R X)
    (hi : _root_.GlobalTheory.FinWeil.idx A B ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A := by
  unfold _root_.GlobalTheory.FinWeil.idx at hi
  rw [AddSubgroup.relIndex, AddSubgroup.index] at hi
  haveI := Nat.finite_of_card_ne_zero hi
  let e := Finite.equivFin (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  refine ⟨_, fun i => ((Quotient.out (e.symm i) : B.toAddSubgroup) : X),
    fun i => (Quotient.out (e.symm i) : B.toAddSubgroup).2, ?_⟩
  intro b hb
  refine ⟨e (⟨b, hb⟩ : B.toAddSubgroup), ?_, fun j hj => ?_⟩
  · have := quotient_out_sub_mem A B (e.symm (e (⟨b, hb⟩ : B.toAddSubgroup))) ⟨b, hb⟩ (by simp)
    simpa using A.neg_mem this
  · have h1 : ((⟨b, hb⟩ : B.toAddSubgroup) :
        B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = e.symm j := by
      rw [← QuotientAddGroup.out_eq' (e.symm j), quotient_mk_eq_mk_iff_sub_mem]
      simpa using A.neg_mem hj
    rw [h1, Equiv.apply_symm_apply]

end

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private lemma fixes_sumOp_of_selfDual {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
    (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A B : Submodule R X}
    (hB : _root_.GlobalTheory.FinWeil.SelfDual γ B) {v : M} (hv : _root_.GlobalTheory.FinWeil.Fixes W A v) :
    _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v) := by
  intro b hb
  unfold _root_.GlobalTheory.FinWeil.sumOp
  set g : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup → M :=
    fun q => W ((Quotient.out q : B.toAddSubgroup) : X) v with hg
  have hinj : ∀ u : M, W b u = 0 → u = 0 := by
    intro u hu
    have h1 := h.neg_comp b u
    rw [hu, map_zero] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (h.ne_zero _ _)
  have hmap : W b (∑ᶠ q, g q) = ∑ᶠ q, W b (g q) := by
    by_cases hs : (Function.support g).Finite
    · exact map_finsum (W b) hs
    · have hs' : ¬ (Function.support fun q => W b (g q)).Finite := by
        refine fun hfin => hs (hfin.subset fun q hq => ?_)
        exact fun h0 => hq (hinj _ h0)
      rw [finsum_of_infinite_support hs, map_zero, finsum_of_infinite_support hs']
  rw [hmap]
  let c : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup :=
    ((⟨b, hb⟩ : B.toAddSubgroup) : B.toAddSubgroup ⧸ _)
  have hterm : ∀ q, W b (g q) = g (c + q) := by
    intro q
    have hq : ((Quotient.out q : B.toAddSubgroup) : X) ∈ B := (Quotient.out q).2
    rw [hg, h.comp_of_mem hB hb hq v]
    refine (heis_apply_eq_of_sub_mem_of_fixes h hB hv (B.add_mem hb hq) (Quotient.out (c + q)).2
      (quotient_out_sub_mem A B (c + q) (⟨b, hb⟩ + Quotient.out q) ?_)).symm
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  simp_rw [hterm]
  exact finsum_comp_equiv (Equiv.addLeft c)

open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_transversal : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M},
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X),
    _root_.GlobalTheory.FinWeil.SelfDual γ B → (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → ∀ (ι : Type) [Fintype ι]
      (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ i, W (f i) v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card ι) ∧
    (_root_.GlobalTheory.FinWeil.idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧
      ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧
      (∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.Fixes W B (_root_.GlobalTheory.FinWeil.sumOp W A B v)) ∧
      ∀ (c : ℂ) v, _root_.GlobalTheory.FinWeil.sumOp W A B (c • v) = c • _root_.GlobalTheory.FinWeil.sumOp W A B v) ∧
    (B ≤ A → _root_.GlobalTheory.FinWeil.idx A B = 1 ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → _root_.GlobalTheory.FinWeil.sumOp W A B v = v) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hB
  have hunit : ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v → B ≤ A →
      _root_.GlobalTheory.FinWeil.sumOp W A B v = ∑ _i : Unit, W 0 v ∧
        _root_.GlobalTheory.FinWeil.idx A B = Fintype.card Unit := fun v hv hBA =>
    _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv Unit (fun _ => 0) (fun _ => B.zero_mem)
      (fun b hb => ⟨(), by simpa using hBA hb, fun _ _ => rfl⟩)
  refine ⟨fun v hv ι _ f hf ht => _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A B hB v hv ι f hf ht,
    fun hi => ⟨_root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A B hi,
      fun v hv => fixes_sumOp_of_selfDual h hB hv, fun c v => ?_⟩, fun hBA => ?_⟩
  · unfold _root_.GlobalTheory.FinWeil.sumOp
    simp_rw [map_smul]
    exact (smul_finsum c _).symm
  · refine ⟨(hunit 0 (fun a _ => map_zero _) hBA).2.trans (by simp), fun v hv => ?_⟩
    rw [(hunit v hv hBA).1]
    simpa using hv 0 A.zero_mem

end GlobalTheory.FinWeil
