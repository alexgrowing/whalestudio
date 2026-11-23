import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyMapTensorRightMorCompCohomologyConj
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Representation

universe u

section Eval

variable {k G : Type u} [Field k] [Group G]

noncomputable abbrev homRep (T M : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (T.ρ.linHom M.ρ)

theorem homRep_ρ_apply (T M : Rep.{u} k G) (g : G) (f : T →ₗ[k] M) :
    (homRep T M).ρ g f = M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹ :=
  rfl

noncomputable def evalMor (T M : Rep.{u} k G) : T ⊗ homRep T M ⟶ M :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.applyₗ (R := k) (M := T) (M₂ := M)), fun g => by
    ext t f
    change (M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹) (T.ρ g t) = M.ρ g (f t)
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩

theorem evalMor_hom_tmul (T M : Rep.{u} k G) (t : T) (f : T →ₗ[k] M) :
    (evalMor T M).hom (t ⊗ₜ[k] f) = f t :=
  rfl

theorem evalMor_bijective (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    Function.Bijective (evalMor T M).hom := by
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  let b : Module.Basis (Fin 1) k T := Module.finBasisOfFinrankEq k T hT
  set t₀ := b 0
  have ht : ∀ t : T, b.coord 0 t • t₀ = t := fun t => by
    simpa using b.sum_repr t
  have hext : ∀ f g : T →ₗ[k] M, f t₀ = g t₀ → f = g := fun f g h =>
    b.ext fun i => by fin_cases i; exact h
  let φ : TensorProduct k T (T →ₗ[k] M) →ₗ[k] (T →ₗ[k] M) :=
    TensorProduct.lift (LinearMap.lsmul k (T →ₗ[k] M) ∘ₗ b.coord 0)
  have hφ : ∀ x : TensorProduct k T (T →ₗ[k] M), t₀ ⊗ₜ[k] φ x = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t f =>
      simp only [φ, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
      rw [← TensorProduct.smul_tmul, ht]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : φ x = 0 := hext _ _ (by
      rw [← hφ x, evalMor_hom_tmul] at hx
      simpa using hx)
    rw [← hφ x, h0, TensorProduct.tmul_zero]
  · intro m
    refine ⟨t₀ ⊗ₜ[k] b.constr k (fun _ => m), ?_⟩
    change b.constr k (fun _ => m) (b 0) = m
    rw [Module.Basis.constr_basis]

noncomputable def evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    M ⟶ T ⊗ homRep T M :=
  let e := LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap (evalMor_bijective T M hT)
  Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext m
    apply e.injective
    change e (e.symm (M.ρ g m)) = (evalMor T M).hom ((T ⊗ homRep T M).ρ g (e.symm m))
    rw [LinearEquiv.apply_symm_apply, (evalMor T M).hom.isIntertwining]
    change M.ρ g m = M.ρ g (e (e.symm m))
    rw [LinearEquiv.apply_symm_apply]⟩

theorem evalInv_comp_evalMor (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalInv T M hT ≫ evalMor T M = 𝟙 M := by
  ext m
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).apply_symm_apply m

theorem evalMor_comp_evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalMor T M ≫ evalInv T M hT = 𝟙 _ := by
  ext x
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).symm_apply_apply x

end Eval

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G)
  [IsDiscreteRep T] [IsDiscreteRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)

omit [IsTopologicalGroup G] [CompactSpace G] [(P : Subgroup G).Normal] [IsDiscreteRep T]
  [IsDiscreteRep M] in
include hT hM in

theorem homRep_ρ_of_mem (g : (P : Subgroup G)) (f : homRep T M) : (homRep T M).ρ g f = f := by
  apply LinearMap.ext
  intro t
  change M.ρ g (f (T.ρ (g : G)⁻¹ t)) = f t
  rw [hM, show ((g : G)⁻¹) = ((g⁻¹ : (P : Subgroup G)) : G) from rfl, hT]

omit [CompactSpace G] [(P : Subgroup G).Normal] [IsDiscreteRep T] [IsDiscreteRep M] in
include hT hM in

theorem isDiscreteRep_homRep : IsDiscreteRep (homRep T M) :=
  ⟨fun f => Subgroup.isOpen_mono (H₁ := (P : Subgroup G))
    (fun g hg => homRep_ρ_of_mem P T M hT hM ⟨g, hg⟩ f) P.isOpen⟩

theorem bijective_nsmul_of_ne_zero {V : Type*} [AddCommGroup V] [Module k V] {m : ℕ}
    (hm : (m : k) ≠ 0) : Function.Bijective fun v : V => m • v := by
  have h : (fun v : V => m • v) = fun v => (m : k) • v := funext fun v => (Nat.cast_smul_eq_nsmul k m v).symm
  rw [h]
  refine ⟨fun v w hvw => ?_, fun v => ⟨(m : k)⁻¹ • v, by simp [smul_smul, mul_inv_cancel₀ hm]⟩⟩
  have := congrArg (fun x => (m : k)⁻¹ • x) hvw
  simpa [smul_smul, inv_mul_cancel₀ hm] using this

variable [Module.Finite k M] (hTr : Module.finrank k T = 1)
  (hP : ((P : Subgroup G).index : k) ≠ 0)

noncomputable def coprimeTwistEquiv (n : ℕ) :
    haveI := isDiscreteRep_homRep P T M hT hM
    cohomology M n ≃ₗ[k]
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  haveI := isDiscreteRep_homRep P T M hT hM
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  (LinearEquiv.ofLinearMap (cohomologyMap (evalInv T M hTr) n).hom (cohomologyMap (evalMor T M) n).hom
      (by
        rw [← ModuleCat.hom_comp, ← cohomologyMap_comp, evalMor_comp_evalInv, cohomologyMap_id]
        rfl)
      (by
        rw [← ModuleCat.hom_comp, ← cohomologyMap_comp, evalInv_comp_evalMor, cohomologyMap_id]
        rfl)) ≪≫ₗ
    coprimeDescentEquiv P (T ⊗ homRep T M) (bijective_nsmul_of_ne_zero hP) n ≪≫ₗ
    (twistInvariantsEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n).symm

include hTr hP in

theorem finrank_cohomology_eq_finrank_invariants (n : ℕ) :
    Module.finrank k (cohomology M n) = Module.finrank k
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  (coprimeTwistEquiv P T M hT hM hTr hP n).finrank_eq

end Descent

end GroundTheory.ProfCoh
