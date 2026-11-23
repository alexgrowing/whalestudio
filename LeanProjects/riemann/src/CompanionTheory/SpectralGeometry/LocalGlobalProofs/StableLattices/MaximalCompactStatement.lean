import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgKMaj

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_riesz (l : E →ₗ[ℂ] ℂ) : ∃ η : E, ∀ x, l x = ⟪η, x⟫_ℂ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  refine ⟨(InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap l), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem sum_sq_eq_of_basis {ι κ : Type*} [Fintype ι] [Fintype κ] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) :
    ∑ i, ‖l (b i)‖ ^ 2 = ∑ j, ‖l (c j)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, c.sum_sq_norm_inner_left]

theorem sq_le_of_basis {ι : Type*} [Fintype ι] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (x : E) :
    ‖l x‖ ^ 2 ≤ ‖x‖ ^ 2 * ∑ i, ‖l (b i)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, ← mul_pow, mul_comm ‖x‖]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm η x) 2

end Abstract

theorem sum_enorm_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∑ i, ‖z i‖ₑ ^ 2 = ENNReal.ofReal (∑ i, ‖z i‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem lintegral_enorm_sq_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (h : MemLp f 2 μ) : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have h1 := h.eLpNorm_lt_top
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h2
  rw [← h2]
  exact ENNReal.pow_lt_top h1

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_coef {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => ⟪ξ, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ) := by
  have h : Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) :=
    (hU.2.2 v).comp_continuous continuous_uMat (fun g => g.2)
  exact continuous_const.inner h

theorem sum_sq_translate {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : Formalism.MainNotions.S.IsKStableOn ε σ S)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ S) (ξ : H) (g k : Formalism.REAL.UJ ε)
    (hk : k ∈ Formalism.REAL.KG ε) :
    ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat (g * k)) (b i : H)⟫_ℂ‖ ^ 2 =
      ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ‖ ^ 2 := by
  have hkK : Formalism.MainNotions.S.umat k ∈ Formalism.REAL.Kset ε := hk
  let T : S →ₗᵢ[ℂ] S :=
    { toLinearMap := ((σ (Formalism.MainNotions.S.umat k) : H →ₗ[ℂ] H).comp S.subtype).codRestrict S
        (fun x => hst _ hkK _ x.2)
      norm_map' := fun x => hU.2.1 _ k.2 _ }
  let Te : S ≃ₗᵢ[ℂ] S := T.toLinearIsometryEquiv rfl
  let l : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [inner_smul_right] }
  have hmul : ∀ x : H, σ (Formalism.MainNotions.S.umat (g * k)) x = σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat k) x) := by
    intro x
    have : Formalism.MainNotions.S.umat (g * k) = Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat k := rfl
    rw [this, hU.1.2 _ g.2 _ k.2]
    rfl
  have h := sum_sq_eq_of_basis l (b.map Te) b
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [hmul, OrthonormalBasis.map_apply]
  rfl

theorem kMaj : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  intro n ε H _ _ _ σ D E hK hU hS u ξ
  obtain ⟨S, hfd, huS, hst⟩ := (hK.mem u).1 u.2
  haveI := hfd
  let b := stdOrthonormalBasis ℂ S
  let c : Formalism.REAL.UJ ε → Fin (Module.finrank ℂ S) → ℂ := fun g i => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ
  have hcm : ∀ i, Measurable fun g => ‖c g i‖ₑ ^ 2 := fun i =>
    (continuous_coef hU ξ (b i : H)).measurable.enorm.pow_const 2
  refine ⟨fun g => ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖c g i‖ₑ ^ 2, ?_, ?_, ?_, ?_⟩
  · exact (Finset.measurable_sum _ fun i _ => hcm i).const_mul _
  · intro g k hk
    simp only [sum_enorm_sq]
    congr 2
    exact sum_sq_translate hU hst b ξ g k hk
  · rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hcm i),
      lintegral_finset_sum _ fun i _ => hcm i]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
    exact lintegral_enorm_sq_lt_top (hS (b i : H) ξ)
  · intro g
    let l : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
        map_add' := fun x y => by simp [inner_add_right]
        map_smul' := fun c x => by simp [inner_smul_right] }
    have h := sq_le_of_basis l b ⟨(u : H), huS⟩
    show ‖l ⟨(u : H), huS⟩‖ₑ ^ 2 ≤ ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖l (b i)‖ₑ ^ 2
    rw [sum_enorm_sq, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h

end GlobalTheory.CompanionTheory.RgKMaj
