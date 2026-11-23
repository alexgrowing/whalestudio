import Mathlib
import GroundTheory.GlobalFields.TateThesis.LatticePoisson

open Module
open scoped RealInnerProductSpace FourierTransform SchwartzMap

namespace GlobalTheory

theorem schwartz_summable_norm_mul_one_add_pow {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (h : 𝓢(V, ℂ)) (N : ℕ) : Summable fun l : Λ => ‖h l‖ * (1 + ‖(l : V)‖) ^ N := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := GroundTheory.Global.exists_norm_le_inv_one_add_pow h (k + N)
  have hs : Summable fun l : Λ => C * ((1 + ‖l‖) ^ k)⁻¹ := by
    apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with l hl
    have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  refine hs.of_nonneg_of_le (fun _ => by positivity) fun l => ?_
  have hp : 0 < 1 + ‖(l : V)‖ := by positivity
  calc ‖h l‖ * (1 + ‖(l : V)‖) ^ N
      ≤ C * ((1 + ‖(l : V)‖) ^ (k + N))⁻¹ * (1 + ‖(l : V)‖) ^ N := by
        gcongr
        exact hg _
    _ = C * ((1 + ‖(l : V)‖) ^ k)⁻¹ := by
        rw [pow_add]
        field_simp
    _ = C * ((1 + ‖l‖) ^ k)⁻¹ := rfl

theorem periodisation_hasSum_fourier_bilinForm {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V) (hP : P.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ) :
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let T : E ≃L[ℝ] V := (toEuclidean (E := V)).symm
  let A₀ : V ≃ₗ[ℝ] E := (P.flip.toDual hP.flip) ≪≫ₗ T.toLinearEquiv.dualMap ≪≫ₗ
    (LinearMap.BilinForm.toDual (innerₗ E) GroundTheory.Global.innerₗ_nondegenerate).symm
  let A : V ≃L[ℝ] E := A₀.toContinuousLinearEquiv
  have hA : ∀ μ y, ⟪A μ, y⟫ = P (T y) μ := by
    intro μ y
    have h := LinearMap.BilinForm.toDual_def (B := innerₗ E) GroundTheory.Global.innerₗ_nondegenerate
      (m := A₀ μ) (n := y)
    have h2 : ⟪A μ, y⟫ = (innerₗ E) (A₀ μ) y := rfl
    rw [h2, ← h]
    simp only [A₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rfl
  let L : Submodule ℤ E := ZLattice.comap ℝ Λ T.toLinearMap
  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ Λ T.toLinearMap))
  haveI : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (ZLattice.comap ℝ Λ T.toLinearMap))
  have hL : ∀ y, y ∈ L ↔ T y ∈ Λ := fun y => Iff.rfl
  let g : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ T f
  have hg : ∀ y, g y = f (T y) := fun y => rfl
  let Λ' : Submodule ℤ V := ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap
  haveI : DiscreteTopology Λ' :=
    inferInstanceAs (DiscreteTopology (ZLattice.comap ℝ (GroundTheory.Global.dualLattice L) A.toLinearMap))
  have hmem : ∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) ↔ A μ ∈ GroundTheory.Global.dualLattice L := by
    intro μ
    rw [GroundTheory.Global.mem_dualLattice]
    constructor
    · intro h y hy
      rw [hA]
      exact h _ ((hL y).mp hy)
    · intro h l hl
      have := h (T.symm l) ((hL _).mpr (by simpa using hl))
      rwa [hA, T.apply_symm_apply] at this
  let h : 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ A (𝓕 g)
  have hh : ∀ μ, h μ = 𝓕 (g : E → ℂ) (A μ) := fun μ => rfl
  refine ⟨fun μ => (ZLattice.covolume L)⁻¹ • h μ, fun N => ?_, fun x => ?_⟩
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ Λ' := Equiv.subtypeEquivRight hmem
    have hs := (e.summable_iff.mpr
      (schwartz_summable_norm_mul_one_add_pow Λ' h N)).mul_left ‖(ZLattice.covolume L)⁻¹‖
    refine hs.congr fun μ => ?_
    rw [norm_smul, mul_assoc]
    rfl
  · let e : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} ≃ GroundTheory.Global.dualLattice L :=
      A.toEquiv.subtypeEquiv hmem
    let e' : L ≃ Λ := T.toEquiv.subtypeEquiv hL
    have hs := e.hasSum_iff.mpr
      (GroundTheory.Global.LatticePoisson.hasSum_smul_fourier (L := L) g (T.symm x))
    have hper : GroundTheory.Global.LatticePoisson.per L g (T.symm x) = ∑' l : Λ, f (x + l) := by
      rw [GroundTheory.Global.LatticePoisson.per, ← e'.tsum_eq]
      refine tsum_congr fun l => ?_
      rw [hg, map_add, T.apply_symm_apply]
      rfl
    rw [hper] at hs
    convert hs using 1
    funext μ
    have he : (e μ : E) = A μ := rfl
    simp only [Function.comp_apply, he, hA, T.apply_symm_apply, hh, Real.fourierChar_apply,
      smul_mul_assoc]
    congr 3
    push_cast
    ring

end GlobalTheory
