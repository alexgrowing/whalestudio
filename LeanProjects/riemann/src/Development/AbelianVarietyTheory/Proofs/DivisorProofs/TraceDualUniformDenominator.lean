import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.DenomTrace

theorem clear_denominators {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]
    (y : ι → E) : ∃ D : ℕ, D ≠ 0 ∧ ∀ i, IsIntegral ℤ ((D : E) * y i) := by
  classical
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image y)
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · refine ⟨k, by exact_mod_cast hd, fun i => ?_⟩
    have := h (y i) (by simp)
    simpa [zsmul_eq_mul] using this
  · refine ⟨k, by simpa using hd, fun i => ?_⟩
    have := (h (y i) (by simp)).neg
    simpa [zsmul_eq_mul] using this

theorem trace_dual_integral {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Module.Basis ι ℚ E) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, (∀ l, ∃ z : ℤ, Algebra.trace ℚ E (x * c l) = z) →
      IsIntegral ℤ ((D : E) * x) := by
  classical
  let cd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) c
  obtain ⟨D, hD, h⟩ := clear_denominators (fun l => cd l)
  refine ⟨D, hD, fun x hx => ?_⟩
  choose z hz using hx
  have hx : x = ∑ l, (z l : E) * cd l := by
    conv_lhs => rw [← cd.sum_repr x]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, hz l,
      Algebra.smul_def]
    simp
  rw [hx, Finset.mul_sum]
  refine IsIntegral.sum _ fun l _ => ?_
  have : (D : E) * ((z l : E) * cd l) = (z l : E) * ((D : E) * cd l) := by ring
  rw [this]
  have h2 := (isIntegral_algebraMap (R := ℤ) (A := E) (x := z l)).mul (h l)
  simpa using h2

theorem integral_traces_bounded_denominators : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E), A.det ≠ 0 →
    ∃ (m : ℕ) (β : Fin m → Fin n → 𝓞 E) (D : ℕ), D ≠ 0 ∧ ∀ ξ : Fin n → E,
      (∀ j, ∃ z : ℤ, Algebra.trace ℚ E (ξ ⬝ᵥ A *ᵥ fun i => σ (β j i)) = z) → ∀ i, ∃ o : 𝓞 E, (D : E) * ξ i = o := by
  intro E _ _ σ n A hA
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b := RingOfIntegers.basis E
  let f : E →ₗ[ℚ] E := σ.toRatAlgHom.toLinearMap
  have hf : Function.Injective f := σ.injective
  let c := (integralBasis E).map (LinearEquiv.ofInjectiveEndo f hf)
  have hc : ∀ l, c l = σ (b l) := by
    intro l
    simp [c, f, b, integralBasis_apply]
  obtain ⟨D₁, hD₁, h₁⟩ := trace_dual_integral c
  obtain ⟨D₂, hD₂, h₂⟩ := clear_denominators (fun p : Fin n × Fin n => A⁻¹ p.1 p.2)
  let e := (Fintype.equivFin (Fin n × ι)).symm
  refine ⟨Fintype.card (Fin n × ι), fun j => Pi.single (e j).1 (b (e j).2), D₁ * D₂,
    mul_ne_zero hD₁ hD₂, ?_⟩
  intro ξ hξ
  have hsingle : ∀ (k : Fin n) (x : 𝓞 E),
      (fun i => σ (((Pi.single k x : Fin n → 𝓞 E) i : 𝓞 E) : E)) = Pi.single k (σ x) := by
    intro k x
    funext i
    by_cases h : i = k
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hv : ∀ k l, ∃ z : ℤ, Algebra.trace ℚ E ((ξ ᵥ* A) k * c l) = z := by
    intro k l
    obtain ⟨z, hz⟩ := hξ (e.symm (k, l))
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    simp only [Equiv.apply_symm_apply]
    rw [hsingle, Matrix.dotProduct_mulVec, dotProduct_single, hc]
  have hvint : ∀ k, IsIntegral ℤ ((D₁ : E) * (ξ ᵥ* A) k) := fun k => h₁ _ (hv k)
  have hξv : ξ = (ξ ᵥ* A) ᵥ* A⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA),
      Matrix.vecMul_one]
  intro i
  have key : ((D₁ * D₂ : ℕ) : E) * ξ i
      = ∑ k, ((D₁ : E) * (ξ ᵥ* A) k) * ((D₂ : E) * A⁻¹ k i) := by
    conv_lhs => rw [hξv]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hint : IsIntegral ℤ (((D₁ * D₂ : ℕ) : E) * ξ i) := by
    rw [key]
    exact IsIntegral.sum _ fun k _ => (hvint k).mul (h₂ (k, i))
  exact ⟨⟨_, hint⟩, rfl⟩

end GlobalTheory.DenomTrace
