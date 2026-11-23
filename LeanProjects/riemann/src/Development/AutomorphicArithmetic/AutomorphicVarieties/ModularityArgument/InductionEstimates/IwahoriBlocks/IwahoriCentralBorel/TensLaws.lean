import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem coef_mem {A B ι : Type} (X : Submodule ℂ (A → ℂ)) (s : Finset ι) (φ : ι → A → ℂ) (ψ : ι → B → ℂ)
    (hψ : LinearIndependent ℂ ψ) (h : ∀ b, (fun a => ∑ i ∈ s, φ i a * ψ i b) ∈ X) : ∀ i ∈ s, φ i ∈ X := by
  intro i hi
  by_contra hn
  obtain ⟨f, hf, hX⟩ := Submodule.exists_le_ker_of_notMem hn
  have h0 : ∑ j ∈ s, f (φ j) • ψ j = 0 := by
    funext b
    have h1 : f (fun a => ∑ i ∈ s, φ i a * ψ i b) = 0 := hX (h b)
    have h2 : (fun a => ∑ i ∈ s, φ i a * ψ i b) = ∑ i ∈ s, ψ i b • φ i := by
      funext a
      simp [Finset.sum_apply, mul_comm]
    rw [h2, map_sum] at h1
    simpa [Finset.sum_apply, mul_comm] using h1
  exact hf (linearIndependent_iff'.1 hψ s _ h0 i hi)

private noncomputable def prodMap {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    X₁ ⊗[ℂ] X₂ →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ ψ x => φ.1 x.1 * ψ.1 x.2)
    (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
    (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))

private theorem prodMap_tmul {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (φ : X₁) (ψ : X₂) :
    prodMap X₁ X₂ (φ ⊗ₜ ψ) = fun x => φ.1 x.1 * ψ.1 x.2 := by
  simp only [prodMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

private theorem prodMap_inj {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    Function.Injective (prodMap X₁ X₂) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  let β := Module.Basis.ofVectorSpace ℂ X₂
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β t
  have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
    β.linearIndependent.map' X₂.subtype (Submodule.ker_subtype _)
  have hc := coef_mem (⊥ : Submodule ℂ (A → ℂ)) c.support (fun i => (c i).1) (fun i => (β i).1) hβ (by
    intro b
    rw [Submodule.mem_bot]
    funext a
    have := congrFun ht (a, b)
    simpa [Finsupp.sum, map_sum, prodMap_tmul, Finset.sum_apply] using this)
  refine Finset.sum_eq_zero fun i hi => ?_
  have : c i = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 (hc i hi))
  simp [this]

private theorem prodMap_range {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    LinearMap.range (prodMap X₁ X₂) = tensFn X₁ X₂ := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ => exact Submodule.subset_span ⟨φ.1, φ.2, ψ.1, ψ.2, prodMap_tmul X₁ X₂ φ ψ⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
    exact ⟨⟨φ, hφ⟩ ⊗ₜ ⟨ψ, hψ⟩, prodMap_tmul X₁ X₂ _ _⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensLaws :
    ∀ {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)), (∃ e : X₁ ⊗[ℂ] X₂ ≃ₗ[ℂ] tensFn X₁ X₂, ∀ φ ψ x, (e (φ ⊗ₜ ψ)).1 x = φ.1 x.1 * ψ.1 x.2) ∧
      ∀ (F : A × B → ℂ) (d : ℕ) (φ : Fin d → A → ℂ) (ψ : Fin d → B → ℂ), (∀ x, F x = ∑ i, φ i x.1 * ψ i x.2) →
        (∀ b, (fun a => F (a, b)) ∈ X₁) → (∀ a, (fun b => F (a, b)) ∈ X₂) → F ∈ tensFn X₁ X₂ := by
  intro A B X₁ X₂
  refine ⟨⟨(LinearEquiv.ofInjective _ (prodMap_inj X₁ X₂)).trans (LinearEquiv.ofEq _ _ (prodMap_range X₁ X₂)), ?_⟩, ?_⟩
  · intro φ ψ x
    exact congrFun (prodMap_tmul X₁ X₂ φ ψ) x
  · intro F d φ ψ hF h₁ h₂
    let W : Submodule ℂ (B → ℂ) := X₂ ⊓ Submodule.span ℂ (Set.range ψ)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
    have hW : ∀ a, (fun b => F (a, b)) ∈ W := by
      intro a
      refine ⟨h₂ a, ?_⟩
      have : (fun b => F (a, b)) = ∑ i, φ i a • ψ i := by
        funext b
        simp [hF, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let β := Module.finBasis ℂ W
    have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
      β.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
    have hrep : ∀ a b, F (a, b) = ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b := by
      intro a b
      have := congrFun (congrArg Subtype.val (β.sum_repr ⟨_, hW a⟩)) b
      rw [Submodule.coe_sum, Finset.sum_apply] at this
      exact this.symm
    have hc := coef_mem X₁ Finset.univ (fun i a => β.repr ⟨_, hW a⟩ i) (fun i => (β i).1) hβ (by
      intro b
      have : (fun a => ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b) = fun a => F (a, b) := by
        funext a
        exact (hrep a b).symm
      rw [this]
      exact h₁ b)
    have : F = ∑ i, fun x : A × B => β.repr ⟨_, hW x.1⟩ i * (β i).1 x.2 := by
      funext x
      rw [Finset.sum_apply]
      exact hrep x.1 x.2
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, hc i (Finset.mem_univ i), _, (β i).2.1, rfl⟩
