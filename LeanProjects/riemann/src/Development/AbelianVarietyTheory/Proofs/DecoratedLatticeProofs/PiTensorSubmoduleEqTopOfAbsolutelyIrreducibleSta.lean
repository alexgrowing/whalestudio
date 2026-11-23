import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurAndTensorSubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem position_add (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f + g) = intersection_update_fsHerm_neg_one i f + intersection_update_fsHerm_neg_one i g := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, position_tprod, LinearMap.add_apply]
  rw [← MultilinearMap.map_update_add]

theorem position_mul (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f * g) = intersection_update_fsHerm_neg_one i f ∘ₗ intersection_update_fsHerm_neg_one i g := by
  ext v
  simp [position_tprod]

theorem position_algebraMap (i : ι) (c : ℂ) :
    intersection_update_fsHerm_neg_one i (algebraMap ℂ (Module.End ℂ (K i)) c) = c • LinearMap.id := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, position_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  rw [Module.algebraMap_end_apply, MultilinearMap.map_update_smul, Function.update_eq_self]

theorem stable_adjoin_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i))
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    {r : Module.End ℂ (K i)} (hr : r ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ y ∈ N, intersection_update_fsHerm_neg_one i r y ∈ N := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g
  | algebraMap c =>
    intro y hy
    rw [position_algebraMap]
    exact N.smul_mem c hy
  | add x y _ _ hx hy =>
    intro z hz
    rw [position_add]
    exact N.add_mem (hx z hz) (hy z hz)
  | mul x y _ _ hx hy =>
    intro z hz
    rw [position_mul]
    exact hx _ (hy z hz)

theorem exists_finset_position (i : ι) (t : ⨂[ℂ] j, K j) :
    ∃ s : Finset (K i), ∀ f g : Module.End ℂ (K i), (∀ m ∈ s, f m = g m) → intersection_update_fsHerm_neg_one i f t = intersection_update_fsHerm_neg_one i g t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    refine ⟨{u i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, position_tprod, position_tprod, h (u i) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun f g h => ?_⟩
    rw [map_add, map_add, hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      hs' f g fun m hm => h m (Finset.mem_union_right _ hm)]

theorem eq_zero_of_subsingleton (i : ι) [Subsingleton (K i)] (t : ⨂[ℂ] j, K j) : t = 0 := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [MultilinearMap.map_coord_zero _ i (Subsingleton.elim _ _), smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end GlobalTheory.TensorIrr

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem stable_all_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i)) (ha : AbsIrr a) [Nontrivial (K i)]
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    (f : Module.End ℂ (K i)) : ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := by
  intro y hy
  obtain ⟨s, hs⟩ := exists_finset_position i y
  obtain ⟨r, hr, hfr⟩ := GlobalTheory.IrrTensor.density a ha.1 ha.2 f s
  rw [hs f r hfr]
  exact stable_adjoin_position i a N hN hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] j, K j))
    (hN : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N) (f : ∀ i, Module.End ℂ (K i)) :
    ∀ y ∈ N, PiTensorProduct.map f y ∈ N := by
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      intro y hy
      rw [this, LinearMap.comp_apply]
      exact hN i (f i) _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

theorem eq_top_of_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  intro ι _ K _ _ G a ha N hN hne
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnt : ∀ i, Nontrivial (K i) := by
    intro i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx0 (eq_zero_of_subsingleton i x)
  have hall : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := fun i f =>
    stable_all_position i (a i) (ha i) N (hN i) f
  obtain ⟨w, hw⟩ : ∃ w, Scal.tform w x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (Scal.eq_of_tform fun w => by rw [h w, map_zero])
  have htp : ∀ v : ∀ i, K i, PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (v i)) =
        (Scal.tform w).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext u
      simp [Scal.tform_tprod, MultilinearMap.map_smul_univ]
    have h1 := stable_map N hall (fun i => (w i).smulRight (v i)) x hxN
    rw [hm, LinearMap.smulRight_apply] at h1
    have h2 := N.smul_mem (Scal.tform w x)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hw, one_smul] at h2
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact htp v

end GlobalTheory.TensorIrr
