import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsRadicalTorusModulus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem TorusModulus.commute (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by
  obtain ⟨hkx, hkw⟩ := Subgroup.mem_inf.1 hk
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  refine matrix_ext_mulVec fun z => ?_
  have hH := (h2 w).1
  have hAA : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.1, map_zero]
  have hBB : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.2.1, map_zero]
  have hAB : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
    rw [hForm, ← h1 w, hp.2.2, map_one]
  have hBA : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hAB, map_one]
  have hKu : (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w :=
    mem_archUnitary.1 k.2 w
  set H := gramAt h v w
  set A := vecAt v x₀ w
  set B := vecAt v w₀ w
  set G := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set K := ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  have hKA : K *ᵥ A = A := hkx w
  have hKB : K *ᵥ B = B := hkw w
  set y := z - hForm H B z • A - hForm H A z • B with hy
  have hyA : hForm H A y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hAA, hAB]
    ring
  have hyB : hForm H B y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hBA, hBB]
    ring
  have hKyA : hForm H A (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu A y
    rw [hKA] at e
    rw [e, hyA]
  have hKyB : hForm H B (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu B y
    rw [hKB] at e
    rw [e, hyB]
  have hGy : G *ᵥ y = y := hgY w y hyA hyB
  have hGKy : G *ᵥ (K *ᵥ y) = K *ᵥ y := hgY w _ hKyA hKyB
  have hGA : G *ᵥ A = a w • A := hgx w
  have hGB : G *ᵥ B = (starRingEnd ℂ (a w))⁻¹ • B := hgw w
  have hz : z = y + hForm H B z • A + hForm H A z • B := by rw [hy]; abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz]
  simp only [mulVec_add, mulVec_smul, hKA, hKB, hGy, hGKy, hGA, hGB]

theorem TorusModulus.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by
  classical
  intro x₀ w₀ hp g a hgx hgw hgY ν _ f hf
  have : FiniteDimensional E W := Module.Finite.of_basis v
  obtain ⟨h', hh'⟩ := h3 x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  obtain ⟨i, q, hic, hqc, hqi, hker, hiw, -⟩ := h4 x₀ w₀ hp h' hh' _ v'
  let τ : archUnitary h' v' →* archUnitary h v := (vecFixGroup h v x₀).subtype.comp i
  have hτc : Continuous τ := continuous_subtype_val.comp hic
  have hτmem : ∀ t, τ t ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀ :=
    fun t => Subgroup.mem_inf.2 ⟨(i t).2, hiw t⟩
  have hnorm : ∀ t, ∀ x ∈ unipRadical h v x₀, τ t * x * (τ t)⁻¹ ∈ unipRadical h v x₀ := by
    intro t x hx
    have hxP : x ∈ vecFixGroup h v x₀ := unipRadical_le_vecFixGroup h v x₀ hx
    have e := (hker (i t * ⟨x, hxP⟩ * (i t)⁻¹)).1 (by
      rw [map_mul, map_mul, map_inv, hqi, (hker ⟨x, hxP⟩).2 hx, mul_one, mul_inv_cancel])
    simpa [τ] using e
  have hinj : ∀ t, τ t ∈ unipRadical h v x₀ → t = 1 := by
    intro t ht
    rw [← hqi t]
    exact (hker (i t)).2 ht
  have hdec : ∀ p : vecFixGroup h v x₀, (p : archUnitary h v) * (τ (q p))⁻¹ ∈ unipRadical h v x₀ := by
    intro p
    have e := (hker (p * (i (q p))⁻¹)).1 (by rw [map_mul, map_inv, hqi, mul_inv_cancel])
    simpa [τ] using e
  let νN : Measure (unipRadical h v x₀) := Measure.haar
  let ρ : Measure (archUnitary h' v') := Measure.haar
  have hδ : ∀ (t : archUnitary h' v') (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂νN = ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f x ∂νN := by
    intro t f hf
    have e := h5 x₀ w₀ hp νN (τ t) (hτmem t)
    have hm : Measurable fun n : unipRadical h v x₀ => τ t * (n : archUnitary h v) * (τ t)⁻¹ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [ENNReal.coe_one, one_mul, ← lintegral_map hf hm, e, lintegral_map hf measurable_subtype_coe]
  obtain ⟨c, -, hc⟩ := h7 x₀ w₀ h' _ v' (vecFixGroup h v x₀) (unipRadical h v x₀)
    (isClosed_vecFixGroup h v x₀) (isClosed_unipRadical h v x₀) (unipRadical_le_vecFixGroup h v x₀)
    τ q (fun _ => 1) hτc hqc continuous_const (fun t => (i t).2) hnorm hinj hdec ν νN ρ hδ
  have hconj : ∀ t (n : archUnitary h v), g * (n * τ t) * g⁻¹ = g * n * g⁻¹ * τ t := by
    intro t n
    have e : τ t * g⁻¹ = g⁻¹ * τ t := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, TorusModulus.commute h v h1 h2 hp g a hgx hgw hgY _
        (hτmem t), mul_inv_cancel_right]
    calc g * (n * τ t) * g⁻¹ = g * n * (τ t * g⁻¹) := by group
      _ = g * n * (g⁻¹ * τ t) := by rw [e]
      _ = g * n * g⁻¹ * τ t := by group
  set K := ∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))
  have hφ : Measurable fun y : archUnitary h v => f (g * y * g⁻¹) :=
    hf.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have step : ∀ t, ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN =
      K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN := by
    intro t
    simp_rw [hconj t]
    exact h6 x₀ w₀ hp g a hgx hgw hgY νN (fun y => f (y * τ t))
      (hf.comp (continuous_id.mul continuous_const).measurable)
  have hmeas : Measurable fun t => ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN :=
    Measurable.lintegral_prod_right' (f := fun p : archUnitary h' v' × unipRadical h v x₀ =>
      f (p.2 * τ p.1)) (hf.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hτc.comp continuous_fst)).measurable)
  calc ∫⁻ x, f (g * x * g⁻¹) ∂ν
      = c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN ∂ρ := hc _ hφ
    _ = c * ∫⁻ t, K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ := by
        simp_rw [ENNReal.coe_one, one_mul, step]
    _ = K * (c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ) := by
        rw [lintegral_const_mul _ hmeas]
        simp only [ENNReal.coe_one, one_mul]
        ring
    _ = K * ∫⁻ x, f x ∂ν := by rw [hc f hf]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
