import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EndoApplyEq
open Polynomial

namespace GlobalTheory.SimpleCharIndep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

theorem linearIndependent_trace : ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Fintype ι] (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, Module A (M i)] [∀ i, IsScalarTower ℂ A (M i)] [∀ i, Module.Finite ℂ (M i)], (∀ i, IsSimpleModule A (M i)) → (∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j) → LinearIndependent ℂ fun (i : ι) (a : A) => LinearMap.trace ℂ (M i) (Algebra.lsmul ℂ ℂ (M i) a) := by
  intro A _ _ ι _ M _ _ _ _ _ hs hne
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀
  have hzero : ∀ i j, i ≠ j → ∀ f : M i →ₗ[A] M j, f = 0 := fun i j hij f =>
    (f.bijective_or_eq_zero).resolve_left fun hb => hij (hne i j ⟨LinearEquiv.ofBijective f hb⟩)
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (M i))) ℂ (M i) := fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := exists_smul_eq_ite (R := A) M hzero i₀ (fun i => Finset.univ.image (b i))
  have hQ : ∀ i, (Algebra.lsmul ℂ ℂ (M i) x : Module.End ℂ (M i))
      = if i = i₀ then LinearMap.id else 0 := by
    intro i
    refine (b i).ext fun k => ?_
    have h1 := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    by_cases hi : i = i₀
    · simpa [hi] using h1
    · simpa [hi] using h1
  have h := congr_fun hg x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hQ i, if_neg hi, map_zero, mul_zero])
    (by simp)] at h
  rw [hQ i₀, if_pos rfl, LinearMap.trace_id] at h
  haveI := IsSimpleModule.nontrivial A (M i₀)
  have hpos : 0 < Module.finrank ℂ (M i₀) := Module.finrank_pos
  have hne0 : (Module.finrank ℂ (M i₀) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact (mul_eq_zero.1 h).resolve_right hne0

end GlobalTheory.SimpleCharIndep
