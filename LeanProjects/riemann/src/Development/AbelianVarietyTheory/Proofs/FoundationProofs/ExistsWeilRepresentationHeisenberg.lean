import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversalStatement

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.rep_inv_apply {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X) (g : Γ)
    (x : X) : ρ g⁻¹ (ρ g x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.mem_map_rep {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X) (g : Γ)
    (A : Submodule R X) (x : X) :
    x ∈ A.map (ρ g) ↔ ρ g⁻¹ x ∈ A := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [_root_.GlobalTheory.FinWeil.rep_inv_apply]
  · intro hx
    refine ⟨ρ g⁻¹ x, hx, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.selfDual_map_rep {γ : X → X → ℂ} {Γ : Type} [Group Γ]
    (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) {A : Submodule R X} (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A)
    (g : Γ) :
    _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) := by
  intro x
  rw [_root_.GlobalTheory.FinWeil.mem_map_rep, hA (ρ g⁻¹ x)]
  constructor
  · intro H b hb
    rw [← hρ g⁻¹]
    exact H _ ((_root_.GlobalTheory.FinWeil.mem_map_rep ρ g A b).1 hb)
  · intro H a ha
    have key := H (ρ g a) (Submodule.mem_map_of_mem ha)
    rwa [← hρ g⁻¹, _root_.GlobalTheory.FinWeil.rep_inv_apply] at key

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
theorem _root_.GlobalTheory.FinWeil.isHeis_comp_rep {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    {Γ : Type} [Group Γ] (ρ : Γ →* Module.End R X)
    (hρ : ∀ g x y, γ (ρ g x) (ρ g y) = γ x y) (g : Γ) :
    _root_.GlobalTheory.FinWeil.IsHeis σ w γ (fun x => W (ρ g x)) := by
  refine ⟨h.sg_sg, h.w_add,
    h.add_left, h.add_right,
    h.alt, h.adj, fun v => ?_,
    fun x y v => ?_⟩
  · show W (ρ g 0) v = v
    rw [map_zero, h.zero]
  · show W (ρ g x) (W (ρ g y) v) = γ (w • x) y • W (ρ g (x + y)) v
    rw [h.comp, map_add, ← hρ g (w • x) y, LinearMap.map_smul]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem normOp_eq_inv_smul_sumOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M)
    (B C : Submodule R X) (v : M) :
    _root_.GlobalTheory.FinWeil.normOp lam W B C v =
      (lam (_root_.GlobalTheory.FinWeil.idx B C))⁻¹ • _root_.GlobalTheory.FinWeil.sumOp W B C v := rfl

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem exists_linearMap_of_relations (u u' : X → M)
    (hspan : Submodule.span ℂ (Set.range u) = ⊤)
    (hrel : ∀ (s : Finset X) (c : X → ℂ), ∑ i ∈ s, c i • u i = 0 → ∑ i ∈ s, c i • u' i = 0) :
    ∃ L : M →ₗ[ℂ] M, ∀ i, L (u i) = u' i := by
  let T := Finsupp.linearCombination ℂ u
  let T' := Finsupp.linearCombination ℂ u'
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  have hker : LinearMap.ker T ≤ LinearMap.ker T' := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    simp only [T, T', Finsupp.linearCombination_apply, Finsupp.sum] at hf ⊢
    exact hrel _ _ hf
  refine ⟨(LinearMap.ker T).liftQ T' hker ∘ₗ
    (T.quotKerEquivOfSurjective hsurj).symm.toLinearMap, fun i => ?_⟩
  have hq : (T.quotKerEquivOfSurjective hsurj).symm (u i) =
      Submodule.Quotient.mk (Finsupp.single i 1) := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp [T]
  simp [hq, T']

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem apply_translate_eq_smul_of_fixes {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {a : X} (ha : a ∈ A) (x : X) :
    W a (W x e) = γ a x • W x e := by
  rw [h.comm, he a ha]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem translate_eq_smul_of_sub_mem {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {A : Submodule R X}
    {e : M} (he : _root_.GlobalTheory.FinWeil.Fixes W A e) {x y : X} (hxy : x - y ∈ A) :
    W x e = (γ (w • y) (x - y))⁻¹ • W y e := by
  have key := h.comp y (x - y) e
  rw [he _ hxy, add_sub_cancel] at key
  rw [key, smul_smul, inv_mul_cancel₀ (h.ne_zero _ _), one_smul]

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem translate_ne_zero' {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W) {e : M} (he0 : e ≠ 0)
    (x : X) : W x e ≠ 0 := by
  intro h0
  have key := h.neg_comp x e
  rw [h0, map_zero] at key
  exact he0 ((smul_eq_zero.mp key.symm).resolve_left (h.ne_zero _ _))

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in
private theorem sum_smul_translate_eq_zero_of_fixes_selfDual {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W V : X → M →ₗ[ℂ] M} (h : _root_.GlobalTheory.FinWeil.IsHeis σ w γ W)
    (hV : _root_.GlobalTheory.FinWeil.IsHeis σ w γ V) {A : Submodule R X}
    (hA : _root_.GlobalTheory.FinWeil.SelfDual γ A) {e u : M} (he0 : e ≠ 0) (he : _root_.GlobalTheory.FinWeil.Fixes W A e)
    (hu : _root_.GlobalTheory.FinWeil.Fixes V A u) (s : Finset X) :
    ∀ c : X → ℂ, ∑ x ∈ s, c x • W x e = 0 → ∑ x ∈ s, c x • V x u = 0 := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc
  have shift : ∀ (U : X → M →ₗ[ℂ] M) (z : M), _root_.GlobalTheory.FinWeil.IsHeis σ w γ U →
      _root_.GlobalTheory.FinWeil.Fixes U A z → ∀ x₀ ∈ s, ∀ a ∈ A,
      U a (∑ x ∈ s, c x • U x z) - γ a x₀ • ∑ x ∈ s, c x • U x z =
        ∑ x ∈ s.erase x₀, (c x * (γ a x - γ a x₀)) • U x z := by
    intro U z hU hz x₀ hx₀ a ha
    rw [Finset.sum_erase _ (by simp) , map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, apply_translate_eq_smul_of_fixes hU hz ha, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
  have eig : ∀ x₀ ∈ s, ∀ a ∈ A,
      V a (∑ x ∈ s, c x • V x u) = γ a x₀ • ∑ x ∈ s, c x • V x u := by
    intro x₀ hx₀ a ha
    have h1 := shift W e h he x₀ hx₀ a ha
    simp only [hc, map_zero, smul_zero, sub_self] at h1
    have h2 := ih (s.erase x₀) (Finset.erase_ssubset hx₀) _ h1.symm
    have h3 := shift V u hV hu x₀ hx₀ a ha
    rw [h2] at h3
    exact sub_eq_zero.mp h3
  by_cases hcase : ∀ x ∈ s, ∀ y ∈ s, x - y ∈ A
  · rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    have col : ∀ (U : X → M →ₗ[ℂ] M) (z : M), _root_.GlobalTheory.FinWeil.IsHeis σ w γ U →
        _root_.GlobalTheory.FinWeil.Fixes U A z →
        ∑ x ∈ s, c x • U x z = (∑ x ∈ s, c x * (γ (w • x₀) (x - x₀))⁻¹) • U x₀ z := by
      intro U z hU hz
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [translate_eq_smul_of_sub_mem hU hz (hcase x hx x₀ hx₀), smul_smul]
    rw [col W e h he] at hc
    rw [col V u hV hu, (smul_eq_zero.mp hc).resolve_right (translate_ne_zero' h he0 x₀), zero_smul]
  · push_neg at hcase
    obtain ⟨x, hx, y, hy, hxy⟩ := hcase
    have hnot : ¬ ∀ a ∈ A, γ (x - y) a = 1 := fun H => hxy ((hA _).2 H)
    push_neg at hnot
    obtain ⟨a, ha, hne⟩ := hnot
    have hγ : γ a x ≠ γ a y := by
      intro heq
      apply hne
      rw [sub_eq_add_neg, h.add_left, h.neg_left,
        h.swap a x, h.swap a y, heq]
      exact mul_inv_cancel₀ (inv_ne_zero (h.ne_zero _ _))
    have e1 := eig x hx a ha
    have e2 := eig y hy a ha
    rw [e1] at e2
    have hzero : (γ a x - γ a y) • ∑ x ∈ s, c x • V x u = 0 := by
      rw [sub_smul, e2, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hγ)

open Classical in
open scoped BigOperators in
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] in

theorem _root_.GlobalTheory.FinWeil.exists_weil_rep : ∀ {R X M : Type} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ}
    {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ lam : ℕ →* ℂ,
    _root_.GlobalTheory.FinWeil.GoodNorm σ lam → ∀ A : Submodule R X, _root_.GlobalTheory.FinWeil.SelfDual γ A →
    ∀ e : M, e ≠ 0 → _root_.GlobalTheory.FinWeil.Fixes W A e →
    Submodule.span ℂ (Set.range fun x => W x e) = ⊤ → ∀ {Γ : Type} [Group Γ]
    (ρ : Γ →* Module.End R X), (∀ g x y, γ (ρ g x) (ρ g y) = γ x y) →
    (∀ g, _root_.GlobalTheory.FinWeil.idx A (A.map (ρ g)) ≠ 0) →
    ∃ Om : Γ →* Module.End ℂ M, (∀ g x v, Om g (W x v) = W (ρ g x) (Om g v)) ∧
      ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) ∧
        Om g e = _root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A hA e he0 he hspan Γ _ ρ hρ hidx
  have hsd : ∀ g, _root_.GlobalTheory.FinWeil.SelfDual γ (A.map (ρ g)) := fun g =>
    _root_.GlobalTheory.FinWeil.selfDual_map_rep ρ hρ hA g
  have hfixE : ∀ g, _root_.GlobalTheory.FinWeil.Fixes W (A.map (ρ g))
      (_root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e) := by
    intro g b hb
    have key := ((_root_.GlobalTheory.FinWeil.sumOp_transversal h A _ (hsd g)).2.1 (hidx g)).2.1 e he b hb
    rw [normOp_eq_inv_smul_sumOp, map_smul, key]
  have hL : ∀ g, ∃ L : M →ₗ[ℂ] M, ∀ x,
      L (W x e) = W (ρ g x) (_root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e) := by
    intro g
    refine exists_linearMap_of_relations (fun x => W x e)
      (fun x => W (ρ g x) (_root_.GlobalTheory.FinWeil.normOp lam W A (A.map (ρ g)) e)) hspan ?_
    intro s c hc
    exact sum_smul_translate_eq_zero_of_fixes_selfDual h (_root_.GlobalTheory.FinWeil.isHeis_comp_rep h ρ hρ g)
      hA he0 he (fun a ha => hfixE g _ (Submodule.mem_map_of_mem ha)) s c hc
  choose L hLe using hL
  have hLint : ∀ g x v, L g (W x v) = W (ρ g x) (L g v) := by
    intro g x
    have hcomp : (L g).comp (W x) = (W (ρ g x)).comp (L g) := by
      refine LinearMap.ext_on_range hspan fun y => ?_
      simp only [LinearMap.comp_apply]
      rw [h.comp x y e, map_smul, hLe, hLe,
        h.comp (ρ g x) (ρ g y), map_add, ← LinearMap.map_smul (ρ g) w x, hρ]
    intro v
    simpa using LinearMap.congr_fun hcomp v
  have hL1 : L 1 = 1 := by
    refine LinearMap.ext_on_range hspan fun x => ?_
    have hmap : A.map (ρ 1) = A := by
      rw [map_one ρ, Module.End.one_eq_id, Submodule.map_id]
    have hT := (_root_.GlobalTheory.FinWeil.sumOp_transversal h A A hA).2.2 le_rfl
    rw [hLe, hmap, normOp_eq_inv_smul_sumOp, hT.2 e he, hT.1, map_one lam, inv_one, one_smul,
      map_one ρ, Module.End.one_apply, Module.End.one_apply]
  have hLmul : ∀ g k, L (g * k) = L g * L k := by
    intro g k
    refine LinearMap.ext_on_range hspan fun x => ?_
    rw [Module.End.mul_apply, hLe, hLe, hLint, map_mul, Module.End.mul_apply]
    congr 1
    have hmapmul : A.map (ρ g * ρ k) = (A.map (ρ k)).map (ρ g) := by
      rw [Module.End.mul_eq_comp, Submodule.map_comp]
    obtain ⟨n, f, hfB, hfu⟩ := _root_.GlobalTheory.FinWeil.exists_transversal_of_idx_ne_zero A (A.map (ρ k)) (hidx k)
    obtain ⟨hsum, hn⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h A (A.map (ρ k)) (hsd k) e he (Fin n) f hfB hfu
    have hgk := hidx (g * k)
    rw [map_mul, hmapmul] at hgk
    have hsdgk := hsd (g * k)
    rw [map_mul, hmapmul] at hsdgk
    rw [hmapmul, ← _root_.GlobalTheory.FinWeil.normOp_comp h lam hlam A (A.map (ρ g)) _ hA (hsd g)
      hsdgk (hidx g) hgk e he]
    have hmem : ∀ y, ρ g y ∈ A.map (ρ g) ↔ y ∈ A := fun y => by
      rw [_root_.GlobalTheory.FinWeil.mem_map_rep, _root_.GlobalTheory.FinWeil.rep_inv_apply]
    obtain ⟨hsum', hn'⟩ := _root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal h (A.map (ρ g)) ((A.map (ρ k)).map (ρ g))
      hsdgk _ (hfixE g) (Fin n) (fun i => ρ g (f i)) (fun i => Submodule.mem_map_of_mem (hfB i)) (by
        intro b hb
        obtain ⟨b', hb', rfl⟩ := Submodule.mem_map.mp hb
        obtain ⟨i, hi, hiu⟩ := hfu b' hb'
        refine ⟨i, ?_, fun j hj => hiu j ?_⟩
        · dsimp only
          rw [← map_sub, hmem]
          exact hi
        · dsimp only at hj
          rwa [← map_sub, hmem] at hj)
    rw [normOp_eq_inv_smul_sumOp (B := A.map (ρ g)), hsum', hn',
      normOp_eq_inv_smul_sumOp (B := A) (C := A.map (ρ k)), hsum, hn, map_smul, map_sum]
    simp only [hLe]
  refine ⟨{ toFun := L, map_one' := hL1, map_mul' := hLmul }, fun g x v => hLint g x v,
    fun g => ⟨hsd g, ?_⟩⟩
  show L g e = _
  have key := hLe g 0
  rw [h.zero, map_zero, h.zero] at key
  exact key

end GlobalTheory.FinWeil
