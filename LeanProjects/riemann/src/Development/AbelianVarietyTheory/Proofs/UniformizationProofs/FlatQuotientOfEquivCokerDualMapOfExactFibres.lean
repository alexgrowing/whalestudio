import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactDualMapOfExactFibresOfIsRegularLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatCokerOfComplexExactModMaximalIdeal

open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory
namespace DualCokernelFlat

section Modules

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

theorem dual_baseChange_surjective (hs : Surjective (algebraMap A B)) (M : Type) [AddCommGroup M]
    [Module A M] [Module.Projective A M] :
    Surjective (Module.Dual.baseChange B : Module.Dual A M → Module.Dual B (B ⊗[A] M)) := by
  intro g
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A B)
    (g.restrictScalars A ∘ₗ TensorProduct.mk A B M 1) hs
  refine ⟨f, ?_⟩
  ext x
  have := LinearMap.congr_fun hf x
  simpa [Algebra.algebraMap_eq_smul_one] using this

theorem dual_baseChange_eq_zero_iff (M : Type) [AddCommGroup M]
    [Module A M] [Module.Free A M] [Module.Finite A M] (f : Module.Dual A M) :
    Module.Dual.baseChange B f = 0 ↔
      f ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M)) := by
  constructor
  · intro h
    let b := Module.Free.chooseBasis A M
    rw [← b.sum_dual_apply_smul_coord f]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have := LinearMap.congr_fun h (1 ⊗ₜ b i)
    simpa [RingHom.mem_ker, Algebra.algebraMap_eq_smul_one] using this
  · intro h
    refine Submodule.smul_induction_on h (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, ← algebraMap_smul B r, RingHom.mem_ker.mp hr, zero_smul]
    · rw [map_add, hx, hy, add_zero]

theorem dual_baseChange_dualMap {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (a : M →ₗ[A] N) (f : Module.Dual A N) :
    Module.Dual.baseChange B (a.dualMap f) =
      (a.baseChange B).dualMap (Module.Dual.baseChange B f) := by
  ext x
  simp

theorem mem_sup_of_exact (hs : Surjective (algebraMap A B)) {M₀ M₁ M₂ : Type}
    [AddCommGroup M₀] [Module A M₀] [Module.Free A M₀] [Module.Finite A M₀]
    [AddCommGroup M₁] [Module A M₁] [Module.Free A M₁] [Module.Finite A M₁]
    [AddCommGroup M₂] [Module A M₂] [Module.Free A M₂] (a : M₀ →ₗ[A] M₁) (b : M₁ →ₗ[A] M₂)
    (h : Exact (b.baseChange B).dualMap (a.baseChange B).dualMap) (x : Module.Dual A M₁)
    (hx : a.dualMap x ∈ (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₀))) :
    x ∈ LinearMap.range b.dualMap ⊔
      (RingHom.ker (algebraMap A B) • ⊤ : Submodule A (Module.Dual A M₁)) := by
  rw [← dual_baseChange_eq_zero_iff, dual_baseChange_dualMap] at hx
  obtain ⟨y, hy⟩ := (h _).1 hx
  obtain ⟨y, rfl⟩ := dual_baseChange_surjective hs M₂ y
  have : x = b.dualMap y + (x - b.dualMap y) := by abel
  rw [this]
  refine Submodule.add_mem_sup ⟨y, rfl⟩ ?_
  rw [← dual_baseChange_eq_zero_iff, map_sub, dual_baseChange_dualMap, hy, sub_self]

end Modules

theorem mem_sup_of_exact_fibres {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (π : A →+* B) (hs : Surjective π) (g : ℕ) (hg : ringKrullDim B = g)
    (C : CochainComplex (ModuleCat.{0} A) ℕ)
    (hF : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hn : ∃ n, ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : PrimeSpectrum A, RingHom.ker π ≤ p.asIdeal → ∃ (K : Type) (_ : Field K)
      (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
        ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i)
    (i : ℕ) (x : Module.Dual A (C.X (i + 1)))
    (hx : (C.d i (i + 1)).hom.dualMap x ∈
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X i)))) :
    x ∈ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ⊔
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X (i + 1)))) := by
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  let := π.toAlgebra
  have key := GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing B g hg (((ModuleCat.extendScalars π).mapHomologicalComplex _).obj C)
    (fun i => ⟨inferInstanceAs (Module.Free B (B ⊗[A] C.X i)),
      inferInstanceAs (Module.Finite B (B ⊗[A] C.X i))⟩)
    (hn.imp fun n h i hi => (ModuleCat.extendScalars π).map_isZero (h i hi)) (fun q => ?_) i
  · exact mem_sup_of_exact (B := B) hs _ _ key x hx
  obtain ⟨K, _, φ, hφ, hK⟩ := hex (q.comap π) (by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le)
  have hle : RingHom.ker π ≤ RingHom.ker φ := by
    rw [hφ, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  obtain ⟨ψ, rfl⟩ : ∃ ψ : B →+* K, ψ.comp π = φ :=
    ⟨π.liftOfSurjective hs ⟨φ, hle⟩, π.liftOfSurjective_comp hs _⟩
  refine ⟨K, inferInstance, ψ, ?_, fun j hj => ?_⟩
  · apply Ideal.comap_injective_of_surjective π hs
    rw [RingHom.comap_ker, hφ]
    rfl
  · refine (hK j (hj.imp_left fun h h' => h ?_)).of_iso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp π ψ) _).app C)
    have hm : (q.asIdeal.comap π).IsMaximal := by
      have : q.asIdeal.comap π = IsLocalRing.maximalIdeal A := h'
      rw [this]
      infer_instance
    have := (Ideal.comap_isMaximal_of_surjective π hs (K := IsLocalRing.maximalIdeal B))
    apply Ideal.comap_injective_of_surjective π hs
    rw [IsLocalRing.eq_maximalIdeal hm, IsLocalRing.eq_maximalIdeal this]

end DualCokernelFlat

open DualCokernelFlat in

theorem flat_quotient_of_equiv_coker_dualMap_of_exact_fibres :
    ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A]
      [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)]
      [Module.Flat V A] (g : ℕ),
      IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) →
      ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal →
        ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
          ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸
        LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by
  intro V A _ _ _ _ _ _ _ _ _ g hreg hg C hF hn hex I ⟨e⟩
  have hfree := fun i => (hF i).1
  have hfin := fun i => (hF i).2
  have hflat : ∀ i, Module.Flat V (Module.Dual A (C.X i)) := fun i => Module.Flat.trans V A _
  have key := mem_sup_of_exact_fibres (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective g hg C hF
    hn (by rw [Ideal.mk_ker]; exact hex)
  rw [Ideal.mk_ker] at key
  have h := GlobalTheory.flat_coker_of_complex_exact_mod_maximalIdeal V A (fun i => Module.Dual A (C.X i))
    (fun i => (C.d i (i + 1)).hom.dualMap) (fun i f => ?_) (hn.imp fun n h i hi => ?_) key
  · exact Module.Flat.of_linearEquiv (e.restrictScalars V).symm
  · ext x
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← LinearMap.comp_apply (C.d _ _).hom,
      ← ModuleCat.hom_comp, C.d_comp_d]
    simp
  · have := ModuleCat.subsingleton_of_isZero (h i hi)
    infer_instance

end GlobalTheory
