import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairFibres

section Algebra

open Module TensorProduct GlobalTheory.PrincipalPolPairing

variable {R Ω : Type} [CommRing R] [CommRing Ω] [Algebra R Ω]
  {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module Ω M'] [AddCommGroup N'] [Module Ω N']
  {f : M →ₛₗ[algebraMap R Ω] M'} {f' : N →ₛₗ[algebraMap R Ω] N'}

theorem subsingleton_coker₂ [Module.Finite R M] [Module.Projective R M] [Module.Finite R N]
    [Module.Projective R N] (hf : Function.Bijective (GlobalTheory.DeRham.liftSemi f))
    (hf' : Function.Bijective (GlobalTheory.DeRham.liftSemi f')) (θ : Dual R M →ₗ[R] N)
    (φ' : Dual Ω M' →ₗ[Ω] Dual Ω (Dual Ω N')) (hφ : Function.Surjective φ')
    (h : ∀ (x : Dual R M) (y : Dual R N) (x' : Dual Ω M') (y' : Dual Ω N'),
      (∀ c, x' (f c) = algebraMap R Ω (x c)) →
      (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (y (θ x))) :
    Subsingleton (Ω ⊗[R] (N ⧸ LinearMap.range θ)) := by
  let e := LinearEquiv.ofBijective _ hf'
  haveI : Module.Finite Ω N' := Module.Finite.equiv e
  haveI : Module.Projective Ω N' := Module.Projective.of_equiv e
  let π : N' →ₗ[Ω] Ω ⊗[R] (N ⧸ LinearMap.range θ) :=
    (LinearMap.range θ).mkQ.baseChange Ω ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    (LinearMap.baseChange_surjective Ω (Submodule.mkQ_surjective _)).comp e.symm.surjective
  let θ' : Dual Ω M' →ₗ[Ω] N' := (Module.evalEquiv Ω N').symm.toLinearMap ∘ₗ φ'
  have hθ' : Function.Surjective θ' := (Module.evalEquiv Ω N').symm.surjective.comp hφ
  have k : π ∘ₗ θ' = 0 := by
    refine ext_corr hf fun x x' hx ↦ ?_
    have e₁ : θ' x' = f' (θ x) := by
      apply (Module.evalEquiv Ω N').injective
      refine ((Module.evalEquiv Ω N').apply_symm_apply _).trans (ext_corr hf' fun y y' hy ↦ ?_)
      rw [h x y x' y' hx hy, ← hy]
      rfl
    have e₂ : f' (θ x) = e (1 ⊗ₜ θ x) := (one_smul Ω (f' _)).symm
    rw [LinearMap.comp_apply, e₁, e₂]
    simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self θ x), tmul_zero]
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := (hπ.comp hθ') a
  obtain ⟨b, rfl⟩ := (hπ.comp hθ') b
  exact (LinearMap.congr_fun k a).trans (LinearMap.congr_fun k b).symm

end Algebra

open Module

theorem isPerfPair_of_fibres₂ : ∀ (R : Type) [CommRing R] (M N : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N] (φ : Module.Dual R M →ₗ[R] Module.Dual R N →ₗ[R] R), (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω], ∃ (M' N' : Type 1) (_ : AddCommGroup M') (_ : Module Ω M') (_ : AddCommGroup N') (_ : Module Ω N') (f : M →ₛₗ[algebraMap R Ω] M') (f' : N →ₛₗ[algebraMap R Ω] N') (φ' : Module.Dual Ω M' →ₗ[Ω] Module.Dual Ω N' →ₗ[Ω] Ω), Function.Bijective (liftSemi f) ∧ Function.Bijective (liftSemi f') ∧ φ'.IsPerfPair ∧ ∀ (x : Module.Dual R M) (x' : Module.Dual Ω M') (y : Module.Dual R N) (y' : Module.Dual Ω N'), (∀ c, x' (f c) = algebraMap R Ω (x c)) → (∀ c, y' (f' c) = algebraMap R Ω (y c)) → φ' x' y' = algebraMap R Ω (φ x y)) → φ.IsPerfPair := by
  intro R _ M N _ _ _ _ _ _ _ _ φ h
  let E := Module.evalEquiv R M
  let E' := Module.evalEquiv R N
  have ev (z : Dual R (Dual R M)) (y : Dual R M) : y (E.symm z) = z y :=
    LinearMap.congr_fun (E.apply_symm_apply z) y
  have ev' (z : Dual R (Dual R N)) (y : Dual R N) : y (E'.symm z) = z y :=
    LinearMap.congr_fun (E'.apply_symm_apply z) y
  have s₁ : Function.Surjective (E'.symm.toLinearMap ∘ₗ φ) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf hf' _ φ' hp.bijective_left.2 fun x y x' y' hx hy ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev', k x x' y y' hx hy]
  have s₂ : Function.Surjective (E.symm.toLinearMap ∘ₗ φ.flip) := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
    refine GlobalTheory.PrincipalPolPairing.subsingleton_of_fibres (R := R) fun p ↦ ?_
    obtain ⟨M', N', _, _, _, _, f, f', φ', hf, hf', hp, k⟩ := h (AlgebraicClosure p.asIdeal.ResidueField)
    exact subsingleton_coker₂ hf' hf _ φ'.flip hp.bijective_right.2 fun y x y' x' hy hx ↦ by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, LinearMap.flip_apply,
        k x x' y y' hx hy]
  refine LinearMap.IsPerfPair.of_bijective _ ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun z ↦ ?_⟩
  · refine LinearMap.ext fun c ↦ ?_
    obtain ⟨y, rfl⟩ := s₂ c
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ev, LinearMap.flip_apply, hx]
    rfl
  · obtain ⟨x, hx⟩ := s₁ (E'.symm z)
    exact ⟨x, E'.symm.injective hx⟩

end GlobalTheory.PairFibres
