import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.invUnits (b : InfinitePlace E → ℂ) : InfinitePlace E → ℂˣ :=
  fun w => if hb : b w = 0 then 1 else (Units.mk0 (b w) hb)⁻¹

omit [NumberField E] [IsTotallyComplex E] in
theorem LineStabHaar.invUnits_of_ne {b : InfinitePlace E → ℂ} (hb : ∀ w, b w ≠ 0) :
    invUnits b = fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
  funext w
  simp [invUnits, hb w]

omit [NumberField E] [IsTotallyComplex E] in
theorem LineStabHaar.measurable_invUnits : Measurable (invUnits (E := E)) := by
  have h0 : Measurable fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹ := by
    refine measurable_iff_comap_le.2 ?_
    change MeasurableSpace.comap _ (MeasurableSpace.comap Units.val _) ≤ _
    rw [MeasurableSpace.comap_comp]
    have e : (Units.val ∘ fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹) =
        fun z => if z = 0 then 1 else z⁻¹ := by
      funext z
      by_cases hz : z = 0 <;> simp [hz]
    rw [e]
    exact (Measurable.ite (measurableSet_singleton 0) measurable_const measurable_inv).comap_le
  exact measurable_pi_lambda _ fun w => h0.comp (measurable_pi_apply w)

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in

theorem LineStabHaar.two_le_finrank {h : HermitianForm F E W} (v : Basis ι E W) {x₀ w₀ : W}
    (hx₀ : x₀ ≠ 0) (hp : IsHyperbolicPair h x₀ w₀) : 2 ≤ finrank E W := by
  have : Module.Finite E W := Module.Finite.of_basis v
  have hli : LinearIndependent E ![x₀, w₀] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have e := congrArg (h.toSesq x₀) hst
    rw [map_add, map_smul, map_smul, hp.1, hp.2.2, map_zero, smul_zero, zero_add, smul_eq_mul,
      mul_one] at e
    subst e
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx₀, rfl⟩
  simpa using hli.fintype_card_le_finrank

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem LineStabHaar.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : WittPartner.Statement h) (h2 : VecAtNeZero.Statement v)
    (h3 : TorusEmbedding.Statement h v) (h4 : LineEigenvalue.Statement h v)
    (h5 : TorusModulus.Statement h v)
    (h6 : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (h7 : UnitsInvHaar.Statement (InfinitePlace E)) : LineStabHaar.Statement h v := by
  classical
  intro x₀ hx₀ hiso μP _
  obtain ⟨w₀, hxw, hww⟩ := h1 x₀ hx₀ hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨τ₀, hτc, hτ⟩ := h3 x₀ w₀ hp
  obtain ⟨β, hβc, hβ⟩ := h4 x₀ hx₀
  have hN := LineStabHaar.two_le_finrank v hx₀ hp
  have hX := h2 x₀ hx₀
  have act : ∀ (g k : archUnitary h v) w (z : ι → ℂ),
      (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
          (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z) := by
    intro g k w z
    simp [Matrix.mulVec_mulVec]
  have τinv : ∀ a w, ((((τ₀ a)⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = (((a w)⁻¹ : ℂˣ) : ℂ) • vecAt v x₀ w := by
    intro a w
    rw [← map_inv, (hτ a⁻¹ w).1, Pi.inv_apply]
  have hmemP : ∀ t, τ₀ t ∈ lineStab h v x₀ := fun t w => ⟨t w, (hτ t w).1⟩
  have hnorm : ∀ t, ∀ x ∈ vecFixGroup h v x₀, τ₀ t * x * (τ₀ t)⁻¹ ∈ vecFixGroup h v x₀ := by
    intro t x hx w
    rw [act, act, τinv, Matrix.mulVec_smul, Matrix.mulVec_smul, hx w, (hτ t w).1, smul_smul,
      Units.inv_mul, one_smul]
  have hinj : ∀ t, τ₀ t ∈ vecFixGroup h v x₀ → t = 1 := by
    intro t ht
    funext w
    have e := ht w
    rw [(hτ t w).1] at e
    have e' : ((t w : ℂ) - 1) • vecAt v x₀ w = 0 := by rw [sub_smul, one_smul, e, sub_self]
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp e').resolve_right (hX w)))
  have hdec : ∀ p : lineStab h v x₀, (p : archUnitary h v) * (τ₀ (β p))⁻¹ ∈ vecFixGroup h v x₀ := by
    intro p w
    rw [act, τinv, Matrix.mulVec_smul, hβ p w, smul_smul, Units.inv_mul, one_smul]
  set N := finrank E W with hNdef
  let δ : (InfinitePlace E → ℂˣ) → ℝ≥0 := fun t => ∏ w, ‖(((t w)⁻¹ : ℂˣ) : ℂ)‖₊ ^ (2 * (N - 1))
  have hδc : Continuous δ := continuous_finsetProd _ fun w _ =>
    ((Units.continuous_coe_inv.comp (continuous_apply w)).nnnorm).pow _
  have hδcoe : ∀ t, (δ t : ℝ≥0∞) = ∏ w, ‖(t w : ℂ)‖ₑ⁻¹ ^ (2 * (N - 2 + 1)) := by
    intro t
    rw [show N - 2 + 1 = N - 1 by omega, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, Units.val_inv_eq_inv_val, nnnorm_inv,
      ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (t w).ne_zero), enorm_eq_nnnorm]
  let ν₀ : Measure (vecFixGroup h v x₀) := Measure.haar
  let ρ : Measure (InfinitePlace E → ℂˣ) := Measure.haar
  have hδ : ∀ (t : InfinitePlace E → ℂˣ) (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ₀ t * x * (τ₀ t)⁻¹) ∂ν₀ = δ t * ∫⁻ x, f x ∂ν₀ := by
    intro t f hf
    rw [hδcoe, show N - 2 + 1 = N - 1 by omega]
    exact h5 x₀ w₀ hp (τ₀ t) (fun w => (t w : ℂ)) (fun w => (hτ t w).1) (fun w => (hτ t w).2.1)
      (fun w z hz₁ hz₂ => (hτ t w).2.2 z hz₁ hz₂) ν₀ f hf
  obtain ⟨c, hc0, hc⟩ := h6 (lineStab h v x₀) (vecFixGroup h v x₀) (isClosed_lineStab h v x₀)
    (isClosed_vecFixGroup h v x₀) (vecFixGroup_le_lineStab h v x₀) τ₀ β δ hτc hβc hδc hmemP hnorm
    hinj hdec μP ν₀ ρ hδ
  obtain ⟨c', hc'0, hc'⟩ := h7 ρ
  let τ : (InfinitePlace E → ℂ) → archUnitary h v := fun b =>
    if ∀ w, b w ≠ 0 then τ₀ (LineStabHaar.invUnits b) else 1
  have hτb : ∀ b (hb : ∀ w, b w ≠ 0), τ b = τ₀ fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
    intro b hb
    simp only [τ, if_pos hb, LineStabHaar.invUnits_of_ne hb]
  have hset : MeasurableSet {b : InfinitePlace E → ℂ | ∀ w, b w ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w => (measurableSet_singleton (0 : ℂ)).compl.preimage
      (measurable_pi_apply w)
  refine ⟨((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀, τ, Measure.IsHaarMeasure.smul _ (by simp [hc0, hc'0]) ENNReal.coe_ne_top,
    Measurable.ite hset (hτc.measurable.comp LineStabHaar.measurable_invUnits) measurable_const,
    fun b => ?_, fun b hb => ?_, fun φ hφ => ?_⟩
  · by_cases hb : ∀ w, b w ≠ 0
    · rw [hτb b hb]
      exact hmemP _
    · simp only [τ, if_neg hb]
      exact one_mem _
  · funext w
    rw [invApply, hτb b hb, ← map_inv, (hτ _ w).1]
    simp
  · have hg : Measurable fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀ :=
      Measurable.lintegral_prod_right' (f := fun q : (InfinitePlace E → ℂˣ) × vecFixGroup h v x₀ =>
        φ (q.2 * τ₀ q.1)) (hφ.comp ((continuous_subtype_val.comp continuous_snd).mul
          (hτc.comp continuous_fst)).measurable)
    have key := hc' (N - 2) (fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀)
      (fun b => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) hg (fun b hb => by rw [hτb b hb])
    rw [hc φ hφ]
    simp_rw [hδcoe]
    rw [key]
    have e2 : ∀ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
        ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂(((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀) =
        ((c * c' : ℝ≥0) : ℝ≥0∞) * ((∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
          ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) := by
      intro b
      rw [lintegral_smul_measure, smul_eq_mul, mul_left_comm]
    simp_rw [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.coe_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
