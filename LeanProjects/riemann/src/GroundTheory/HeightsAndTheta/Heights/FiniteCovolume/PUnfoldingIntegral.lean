import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnfoldingTorus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [Fintype ι]
  [DecidableEq ι] in

theorem two_le_finrank_of_isotropic [FiniteDimensional E W] (h : HermitianForm F E W) {x₀ : W}
    (hne : x₀ ≠ 0) (hiso : h.toSesq x₀ x₀ = 0) : 2 ≤ finrank E W := by
  by_contra hlt
  have hpos : 0 < finrank E W := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x₀, hne⟩
  have h1 : finrank E W = 1 := by omega
  have hspan := (finrank_eq_one_iff_of_nonzero' x₀ hne).mp h1
  apply hne
  apply h.nonsingular.1
  rw [map_zero]
  ext y
  obtain ⟨c, rfl⟩ := hspan y
  rw [LinearMap.zero_apply, map_smul, hiso, smul_zero]

omit [DecidableEq ι] in

theorem re_form_smul (P : Matrix ι ι ℂ) (b : ℂ) (y : ι → ℂ) :
    (star (b • y) ⬝ᵥ (P *ᵥ (b • y))).re = (star y ⬝ᵥ (P *ᵥ y)).re * ‖b‖ ^ 2 := by
  have hb : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, hb, Complex.re_ofReal_mul, mul_comm]

theorem UnfoldingIntegral.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : UnfoldingTorus.Statement h v)
    (h₂ : TorusIntegralHomogeneous.Statement (InfinitePlace E))
    (h₃ : DiscreteFundamentalDomain.Statement (archUnitary h v)) :
    UnfoldingIntegral.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  have : FiniteDimensional E W := v.finiteDimensional_of_finite

  have hdisc : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨FD, -, hFD⟩ := h₃ μ _ hdisc
  obtain ⟨c, hc0, hctop, hc⟩ := h₁ M μ D La x₀ hLa hx₀ hne hiso
  set y := vecAt v x₀ with hy
  set q : InfinitePlace E → ℝ := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re with hq_def
  have hq : ∀ w, 0 < q w := fun w =>
    (Complex.pos_iff.mp ((M.posDef w).dotProduct_mulVec_pos (VecAtNeZero.proof v x₀ hne w))).1
  obtain ⟨C, hC0, hCtop, hC⟩ := h₂ q hq (finrank E W - 2)

  obtain ⟨k, hk⟩ : ∃ k, finrank E W = k + 2 :=
    ⟨finrank E W - 2, by have := two_le_finrank_of_isotropic h hne hiso; omega⟩
  have hcard : Fintype.card (InfinitePlace E) = finrank ℚ F := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h2
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  have hexp : (2 * (finrank E W - 2) + 2) * Fintype.card (InfinitePlace E) =
      2 * finrank ℚ F * (finrank E W - 1) := by
    rw [hcard, hk, Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
    ring
  refine ⟨FD, hFD, c * C, ENNReal.mul_pos hc0.ne' hC0.ne', ENNReal.mul_lt_top hctop hCtop,
    fun t ht => ?_⟩

  have hset : {b : InfinitePlace E → ℂ | M.len (fun w => b w • y w) < t} =
      {b | ∑ w, q w * ‖b w‖ ^ 2 < t ^ 2} := by
    ext b
    simp only [Set.mem_ofPred_eq, Majorant.len, Real.sqrt_lt' ht, re_form_smul, hq_def,
      mul_comm]
  rw [hc FD hFD t ht, hset, hC t ht, hexp]
  exact (mul_assoc c C _).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
