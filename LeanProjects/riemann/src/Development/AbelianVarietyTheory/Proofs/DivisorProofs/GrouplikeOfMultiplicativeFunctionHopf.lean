import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorFiniteAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HopfPoints

theorem exists_element_eval_eq_character : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (χ : (A →ₐ[R] K) → K), (∀ x y z : A →ₐ[R] K, toConv z = toConv x * toConv y → χ z = χ x * χ y) → (∀ x, χ x ≠ 0) → ∃ a : A, ∀ x : A →ₐ[R] K, x a = χ x := by
  intro R K _ _ _ _ _ _ _ _ A _ _ _ _ _ χ hmul hne
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  obtain ⟨hfin, -, -⟩ := finite_points_separate_rank R K A
  obtain ⟨-, hsep, -⟩ := finite_points_separate_rank R K (A ⊗[R] A)
  obtain ⟨r, a', hr, ha'⟩ := GlobalTheory.exists_element_eval_eq_const_mul_of_finite_points R K A χ
  have hrK : algebraMap R K r ≠ 0 := fun h => hr (hRK (by simpa using h))

  have hcomul : r • comul (R := R) a' = a' ⊗ₜ[R] a' := by
    rw [← sub_eq_zero]
    apply hsep
    intro ψ
    let x : A →ₐ[R] K := ψ.comp Algebra.TensorProduct.includeLeft
    let y : A →ₐ[R] K := ψ.comp Algebra.TensorProduct.includeRight
    have hψ : ψ = Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _) := by
      ext a <;> simp [x, y]
    have hz := hmul x y (toConv x * toConv y).ofConv rfl
    have h1 : ψ (comul (R := R) a') = (toConv x * toConv y).ofConv a' := by
      rw [hψ, AlgHom.convMul_apply]
    have h2 : ψ (a' ⊗ₜ[R] a') = x a' * y a' := by
      rw [hψ]; simp
    rw [map_sub, map_smul, h1, h2, ha', ha', ha', hz, Algebra.smul_def]
    ring
  have hcounit : counit (R := R) a' = r := by
    have h1 := hmul (1 : WithConv (A →ₐ[R] K)).ofConv (1 : WithConv (A →ₐ[R] K)).ofConv
      (1 : WithConv (A →ₐ[R] K)).ofConv (by simp)
    have h2 : χ (1 : WithConv (A →ₐ[R] K)).ofConv = 1 := by
      have := hne (1 : WithConv (A →ₐ[R] K)).ofConv
      exact mul_left_cancel₀ this (by rw [_root_.mul_one]; exact h1.symm)
    have h3 := ha' (1 : WithConv (A →ₐ[R] K)).ofConv
    rw [h2, _root_.mul_one] at h3
    apply hRK
    rw [← h3]
    simp
  let L : CartierDual R A →ₗ[R] K :=
    (algebraMap R K r)⁻¹ • (Algebra.linearMap R K ∘ₗ CartierDual.evalAt R A a')
  have hL : ∀ φ, L φ = (algebraMap R K r)⁻¹ * algebraMap R K (φ a') := fun φ => rfl
  let Φ : CartierDual R A →ₐ[R] K := AlgHom.ofLinearMap L
    (by rw [hL, CartierDual.one_apply, hcounit, inv_mul_cancel₀ hrK])
    (by
      intro φ ψ
      have h : r * (φ * ψ) a' = φ a' * ψ a' := by
        rw [CartierDual.mul_apply, ← smul_eq_mul, ← map_smul, hcomul, CartierDual.pair_tmul_tmul]
      have h' := congrArg (algebraMap R K) h
      rw [map_mul, map_mul] at h'
      rw [hL, hL, hL]
      field_simp
      linear_combination h')
  obtain ⟨g, hg⟩ := exists_algHom_comp_eq (A := R) (K := K) Φ
  obtain ⟨a, ha⟩ := (CartierDual.toBidual_bijective (R := R) (M := A)).2 (toConv g.toLinearMap)
  have hga : ∀ φ : CartierDual R A, φ a = g φ := fun φ => by
    have := congrArg (fun t : CartierDual R (CartierDual R A) => t φ) ha
    exact this
  have hra : a' = r • a := by
    apply CartierDual.eq_of_forall_apply (R := R)
    intro φ
    apply hRK
    have h1 : algebraMap R K (g φ) = L φ := by
      have := congrArg (fun t : CartierDual R A →ₐ[R] K => t φ) hg
      exact this
    rw [map_smul, smul_eq_mul, map_mul, hga, h1, hL, mul_inv_cancel_left₀ hrK]
  refine ⟨a, fun x => mul_left_cancel₀ hrK ?_⟩
  rw [← ha', hra, map_smul, Algebra.smul_def]

end GlobalTheory.HopfPoints
