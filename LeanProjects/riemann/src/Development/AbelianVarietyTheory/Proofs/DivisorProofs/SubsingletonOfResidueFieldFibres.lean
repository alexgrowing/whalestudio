import Mathlib

namespace GlobalTheory

open TensorProduct

open TensorProduct in
open TensorProduct in

theorem _root_.GlobalTheory.subsingleton_of_residueField_fibres (O Q : Type) [CommRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    (h : ∀ q : PrimeSpectrum O, Subsingleton (q.asIdeal.ResidueField ⊗[O] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := O), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  exact not_nontrivial_iff_subsingleton.mpr (h q) hq

open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.surjective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine _root_.GlobalTheory.subsingleton_of_residueField_fibres O _ fun q => ?_
  have htop : LinearMap.range (f.baseChange q.asIdeal.ResidueField) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h q)
  have hex := lTensor_exact q.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective _)
  refine ⟨fun y y' => ?_⟩
  suffices ∀ y : q.asIdeal.ResidueField ⊗[O] (N ⧸ LinearMap.range f), y = 0 by
    rw [this y, this y']
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective q.asIdeal.ResidueField
    (Submodule.mkQ_surjective (LinearMap.range f)) y
  have hx : x ∈ LinearMap.range (f.baseChange q.asIdeal.ResidueField) := htop ▸ Submodule.mem_top
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.baseChange_eq_ltensor]
  exact hex.apply_apply_eq_zero z

theorem injective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    [Module.Finite O M] [Module.Projective O N] (hf : Function.Surjective f)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (TensorProduct O q.asIdeal.ResidueField M) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf

  have hsurj : Function.Surjective s := by
    apply surjective_of_fibre_rank O N M s
    intro q
    have hinj : Function.Injective (s.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := f.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs]
      simp
    rw [LinearMap.finrank_range_of_inj hinj, h q]
  intro a b hab
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  have hy : f (s y) = y := LinearMap.congr_fun hs y
  rw [hx, hy] at hab
  rw [hab]

theorem surjective_injective_of_fibre_rank :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by
  intro O M N _ _ _ _ _ _ f
  exact ⟨surjective_of_fibre_rank O M N f,
    fun _ _ hf h => injective_of_fibre_rank O M N f hf h⟩

end GlobalTheory
