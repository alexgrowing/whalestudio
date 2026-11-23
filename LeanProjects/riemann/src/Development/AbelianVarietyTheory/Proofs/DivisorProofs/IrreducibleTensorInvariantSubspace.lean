import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensSpanIrr

open GlobalTheory.RealLift GlobalTheory.KFixIrr

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem atPl_local_sub (H : ι → Submodule ℂ V) (w : ι) (y : ⨂[ℂ] _ : ι, V) (hy : y ∈ tensSpan H) :
    ∃ s : Finset (H w), ∀ f g : Module.End ℂ V, (∀ m ∈ s, f m = g m) →
      atPl (V := fun _ : ι => V) w f y = atPl (V := fun _ : ι => V) w g y := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨{⟨v w, hv w⟩}, fun f g h => ?_⟩
    rw [GlobalTheory.TensIrr.atPl_tprod, GlobalTheory.TensIrr.atPl_tprod, h ⟨v w, hv w⟩ (Finset.mem_singleton_self _)]
  | zero => exact ⟨∅, fun f g _ => by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun f g h => ?_⟩
    rw [map_add, map_add, hs f g (fun m hm => h m (Finset.mem_union_left _ hm)),
      ht f g (fun m hm => h m (Finset.mem_union_right _ hm))]
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, fun f g h => by rw [map_smul, map_smul, hs f g h]⟩

theorem stable_of_range (H : ι → Submodule ℂ V) (w : ι) [FiniteDimensional ℂ (H w)] [Nontrivial (H w)]
    {Z : Type} (A : Z → Module.End ℂ V) (hA : ∀ z, ∀ v ∈ H w, A z v ∈ H w)
    (hirr : ∀ N : Submodule ℂ V, N ≤ H w → (∀ z, ∀ v ∈ N, A z v ∈ N) → N = ⊥ ∨ N = H w)
    (N : Submodule ℂ (⨂[ℂ] _ : ι, V)) (hle : N ≤ tensSpan H)
    (hN : ∀ z, ∀ T ∈ N, atPl (V := fun _ : ι => V) w (A z) T ∈ N)
    (F : Module.End ℂ V) (hF : ∀ v, F v ∈ H w) :
    ∀ y ∈ N, atPl (V := fun _ : ι => V) w F y ∈ N := by
  classical
  let B : Z → Module.End ℂ (H w) := fun z => (A z).restrict (hA z)
  have hBirr : ∀ M : Submodule ℂ (H w), (∀ z, ∀ y ∈ M, B z y ∈ M) → M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hinj := Submodule.map_injective_of_injective (H w).injective_subtype
    rcases hirr (M.map (H w).subtype) (by simp [Submodule.map_subtype_le]) (by
      rintro z _ ⟨x, hx, rfl⟩
      exact ⟨B z x, hM z x hx, rfl⟩) with h | h
    · left
      apply hinj
      rw [h, Submodule.map_bot]
    · right
      apply hinj
      rw [h, Submodule.map_subtype_top]
  have hBsch : ∀ T : H w →ₗ[ℂ] H w, (∀ z, T ∘ₗ B z = B z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id := by
    intro T hT
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    refine ⟨c, ?_⟩
    rcases hBirr (Module.End.eigenspace T c) (fun z y hy => by
      rw [Module.End.mem_eigenspace_iff] at hy ⊢
      have := LinearMap.congr_fun (hT z) y
      simp only [LinearMap.comp_apply] at this
      rw [this, hy, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · ext x
      have hx : x ∈ Module.End.eigenspace T c := h ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hx
      simp [hx]
  have hadj : ∀ r ∈ Algebra.adjoin ℂ (Set.range A), ∀ y ∈ N, atPl (V := fun _ : ι => V) w r y ∈ N := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hN z
    | algebraMap c =>
      intro y hy
      rw [Algebra.algebraMap_eq_smul_one, GlobalTheory.TensIrr.atPl_smul, GlobalTheory.TensIrr.atPl_one]
      exact N.smul_mem c hy
    | add x y _ _ hx hy =>
      intro z hz
      rw [GlobalTheory.TensIrr.atPl_add]
      exact N.add_mem (hx z hz) (hy z hz)
    | mul x y _ _ hx hy =>
      intro z hz
      rw [GlobalTheory.TensIrr.atPl_mul]
      exact hx _ (hy z hz)
  have hlift : ∀ r ∈ Algebra.adjoin ℂ (Set.range B),
      ∃ r' ∈ Algebra.adjoin ℂ (Set.range A), ∀ x : H w, r' x = (r x : V) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨A z, Algebra.subset_adjoin ⟨z, rfl⟩, fun x => rfl⟩
    | algebraMap c =>
      exact ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, fun x => by
        simp [Algebra.algebraMap_eq_smul_one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun t => by simp [ha', hb']⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a * b, mul_mem ha hb, fun t => by
        rw [Module.End.mul_apply, Module.End.mul_apply, hb', ha']⟩
  intro y hy
  obtain ⟨s, hs⟩ := atPl_local_sub H w y (hle hy)
  let g : Module.End ℂ (H w) := F.restrict (fun v _ => hF v)
  obtain ⟨r, hr, hrg⟩ := GlobalTheory.IrrTensor.density B hBirr hBsch g s
  obtain ⟨r', hr', hr'r⟩ := hlift r hr
  rw [hs F r' (fun m hm => by rw [hr'r m, ← hrg m hm]; rfl)]
  exact hadj r' hr' y hy

theorem tensSpan_irr : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V Z : Type) [AddCommGroup V] [Module ℂ V]
    (A : ι → Z → Module.End ℂ V) (H : ι → Submodule ℂ V), (∀ w, FiniteDimensional ℂ (H w)) → (∀ w, H w ≠ ⊥) →
    (∀ w z, ∀ v ∈ H w, A w z v ∈ H w) →
    (∀ w (N : Submodule ℂ V), N ≤ H w → (∀ z, ∀ v ∈ N, A w z v ∈ N) → N = ⊥ ∨ N = H w) →
    ∀ N : Submodule ℂ (⨂[ℂ] _ : ι, V), N ≤ GlobalTheory.KFixIrr.tensSpan H →
      (∀ w z, ∀ T ∈ N, GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w (A w z) T ∈ N) →
      N = ⊥ ∨ N = GlobalTheory.KFixIrr.tensSpan H := by
  intro ι _ _ V Z _ _ A H hfd hne hA hirr N hle hN
  classical
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.TensIrr.exists_prodForm_ne (V := fun _ : ι => V) y hy0
  refine le_antisymm hle ?_
  rw [tensSpan, Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩
  have hst : ∀ w, ∀ x ∈ N, atPl (V := fun _ : ι => V) w ((ℓ w).smulRight (u w)) x ∈ N := by
    intro w
    haveI : FiniteDimensional ℂ (H w) := hfd w
    haveI : Nontrivial (H w) := Submodule.nontrivial_iff_ne_bot.2 (hne w)
    exact stable_of_range H w (A w) (hA w) (hirr w) N hle (hN w) _
      (fun v => by simpa using (H w).smul_mem (ℓ w v) (hu w))
  have key : ∀ s : Finset ι, ∀ x ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) x ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert a s ha ih =>
      intro x hx
      have e : PiTensorProduct.map (fun i => if i ∈ insert a s then (ℓ i).smulRight (u i) else LinearMap.id) =
          atPl (V := fun _ : ι => V) a ((ℓ a).smulRight (u a)) ∘ₗ
            PiTensorProduct.map (fun i => if i ∈ s then (ℓ i).smulRight (u i) else LinearMap.id) := by
        unfold atPl
        rw [← PiTensorProduct.map_comp]
        congr 1
        funext j
        by_cases h : j = a
        · subst h; simp [ha]
        · simp [Function.update_of_ne h, Finset.mem_insert, h]
      rw [e]
      exact hst a _ (ih x hx)
  have h1 := key Finset.univ y hy
  simp only [Finset.mem_univ, if_true] at h1
  rw [GlobalTheory.TensIrr.map_rankOne] at h1
  have h2 := N.smul_mem (GlobalTheory.TensIrr.prodForm ℓ y)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hℓ, one_smul] at h2

end GlobalTheory.TensSpanIrr

end
