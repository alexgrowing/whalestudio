import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementCartierDualTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HopfFourier

theorem surjective_of_integral_sq_card : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (f : CartierDual R A →ₐc[R] A) (Λ : CartierDual R A) (y : R), (∀ d : CartierDual R A, d * Λ = algebraMap R _ (Coalgebra.counit (R := R) d) * Λ) → Coalgebra.counit (R := R) Λ = y → algebraMap R K y ^ 2 = (Nat.card (A →ₐ[R] K) : K) → Function.Injective f → Function.Surjective f := by
  intro R K _ _ _ _ _ _ _ _ A _ _ _ _ _ f Λ y hΛ hy hN hf
  have hflat : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  let bc := CartierDual.baseChange R K A
  let F : CartierDual K (K ⊗[R] A) →ₐc[K] K ⊗[R] A :=
    (Bialgebra.TensorProduct.map (BialgHom.id K K) f).comp
      (bc.symm : CartierDual K (K ⊗[R] A) →ₐc[K] K ⊗[R] CartierDual R A)
  let ΛK : CartierDual K (K ⊗[R] A) := bc (1 ⊗ₜ Λ)
  have hι : Function.Injective (fun a : A => (1 : K) ⊗ₜ[R] a) := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro a b hab
    apply (TensorProduct.lid R A).symm.injective
    apply h1
    simpa using hab
  have hF : ∀ d : CartierDual R A, F (bc (1 ⊗ₜ d)) = 1 ⊗ₜ f d := by
    intro d
    simp [F]
  have hFinj : Function.Injective F := by
    have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (f : CartierDual R A →ₗ[R] A) hf
    intro u v huv
    apply bc.symm.injective
    apply h1
    exact huv

  have hΛK : ∀ d : CartierDual K (K ⊗[R] A), d * ΛK = algebraMap K _ (Coalgebra.counit (R := K) d) * ΛK := by
    intro d
    obtain ⟨z, rfl⟩ : ∃ z, bc z = d := ⟨bc.symm d, bc.apply_symm_apply d⟩
    have hc : Coalgebra.counit (R := K) (bc z) = Coalgebra.counit (R := K) z :=
      CoalgHomClass.counit_comp_apply bc z
    rw [hc]
    clear hc
    have key : z * (1 ⊗ₜ Λ) = algebraMap K _ (Coalgebra.counit (R := K) z) * (1 ⊗ₜ Λ) := by
      induction z with
      | zero => simp
      | add u v hu hv => rw [add_mul, hu, hv, map_add, map_add, add_mul]
      | tmul k d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hΛ d, _root_.mul_one]
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [ΛK, ← map_mul, key]
    rw [map_mul, AlgHomClass.commutes]
  have hy' : Coalgebra.counit (R := K) ΛK = algebraMap R K y := by
    have hc : Coalgebra.counit (R := K) ΛK = Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] Λ) :=
      CoalgHomClass.counit_comp_apply bc _
    rw [hc, ← hy]
    simp [Algebra.smul_def]
  have hcard : Nat.card (K ⊗[R] A →ₐ[K] K) = Nat.card (A →ₐ[R] K) := by
    refine Nat.card_congr
      { toFun := fun φ => (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight
        invFun := fun g => Algebra.TensorProduct.lift (Algebra.ofId K K) g (fun _ _ => Commute.all _ _)
        left_inv := fun φ => Algebra.TensorProduct.ext' fun k a => by
          have e : (k ⊗ₜ[R] a : K ⊗[R] A) = k • (1 ⊗ₜ a) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
          simp [e]
        right_inv := fun g => AlgHom.ext fun a => by simp }
  have hN' : (Coalgebra.counit (R := K) ΛK) ^ 2 = (Nat.card (K ⊗[R] A →ₐ[K] K) : K) := by
    rw [hy', hcard, hN]
  have hψ : ∀ x : A, toConv (ΛK.ofConv ∘ₗ LinearMap.mulLeft K ((1 : K) ⊗ₜ[R] x)) =
      bc (1 ⊗ₜ toConv (Λ.ofConv ∘ₗ LinearMap.mulLeft R x)) := by
    intro x
    refine WithConv.ext (TensorProduct.AlgebraTensorModule.ext fun k b => ?_)
    simp [ΛK, bc]
  have hT : ∀ d : CartierDual R A, (CartierDual.bidual K (K ⊗[R] A)).symm (CartierDual.map F (bc (1 ⊗ₜ d))) =
      1 ⊗ₜ (CartierDual.bidual R A).symm (CartierDual.map f d) := by
    intro d
    refine CartierDual.eq_of_forall_apply (R := K) fun φ => ?_
    rw [CartierDual.apply_bidual_symm, CartierDual.map_apply]
    obtain ⟨z, rfl⟩ : ∃ z, bc z = φ := ⟨bc.symm φ, bc.apply_symm_apply φ⟩
    have hz : F (bc z) = Bialgebra.TensorProduct.map (BialgHom.id K K) f z := by simp [F]
    rw [hz]
    clear hz
    induction z with
    | zero => simp
    | add u v hu hv => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, hu, hv]
    | tmul k d' => simp [bc, CartierDual.apply_bidual_symm]
  have hS : ∀ a : A, HopfAlgebra.antipode K ((1 : K) ⊗ₜ[R] a) = 1 ⊗ₜ HopfAlgebra.antipode R a := by
    intro a
    simp
  intro a
  have key := GlobalTheory.T.integral_element_cartier_dual_trace K (K ⊗[R] A) F ΛK _ hΛK rfl hN' hFinj (1 ⊗ₜ a)
  rw [hS, hψ, hT, hψ, hF] at key
  exact ⟨_, hι key⟩

end GlobalTheory.HopfFourier
