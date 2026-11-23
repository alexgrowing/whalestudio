import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open MeasureTheory GlobalTheory.CuspRep
open scoped ENNReal Matrix

namespace GlobalTheory.ThetaUnfold

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem theta_unfold_mirabolic (l : Fin a) (_hl : l.val + 1 = a) (P : Subgroup (GL (Fin a) E))
    (hP : ∀ γ : GL (Fin a) E, γ ∈ P ↔ ∀ j, γ.val l j = if j = l then 1 else 0) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)]
    [MeasurableSpace (Fin a → Ad E)] [BorelSpace (Fin a → Ad E)] (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ) :
    (∀ F : GA E a × (Fin a → Ad E) → ℝ≥0∞, Measurable F → (∀ γ g y, F (ratGL E a γ * g, y) = F (g, y)) →
      ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
        ∫⁻ g in 𝓕', F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val) ∂μ) ∧
    ∀ F : GA E a × (Fin a → Ad E) → ℂ, Measurable F → (∀ γ g y, F (ratGL E a γ * g, y) = F (g, y)) →
      ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ < ⊤ →
      (∀ᵐ g ∂μ.restrict 𝓕,
        Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
      IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
      IntegrableOn (fun g => F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val)) 𝓕' μ ∧
      ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F (g, (algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
        ∫ g in 𝓕', F (g, (Pi.single l 1 : Fin a → Ad E) ᵥ* g.val) ∂μ := by
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ P ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 := fun γ => by
    rw [hP, Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
  have he : (Pi.single l 1 : Fin a → Ad E) = algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [he]
  have hc : Measurable fun g : GA E a => (g, (algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E)) ᵥ* g.val) :=
    measurable_id.prodMk (continuous_vecMul _).measurable
  exact ⟨fun F hm hF => lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕' (fun g y => F (g, y)) hF
      (hm.comp hc).aemeasurable,
    fun F hm hF hfin => integral_tsum_vecMul μ hv hP' h𝓕 h𝓕' (fun g y => F (g, y)) hF
      (hm.comp hc).aestronglyMeasurable hfin.ne⟩

omit [NumberField E] in

theorem exists_mirabolic (l : Fin a) :
    ∃ P : Subgroup (GL (Fin a) E), ∀ γ : GL (Fin a) E, γ ∈ P ↔ ∀ j, γ.val l j = if j = l then 1 else 0 := by
  have h : ∀ γ : GL (Fin a) E, (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 ↔
      ∀ j, γ.val l j = if j = l then 1 else 0 := fun γ => by
    rw [Matrix.single_one_vecMul, funext_iff]
    simp only [Pi.single_apply, Matrix.row]
  refine ⟨{ carrier := {γ | (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1}
            mul_mem' := fun {x y} hx hy => ?_, one_mem' := Matrix.vecMul_one _, inv_mem' := fun {x} hx => ?_ }, h⟩
  · simp only [Set.mem_setOf_eq, Units.val_mul, ← Matrix.vecMul_vecMul] at *
    rw [hx, hy]
  · simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

open NumberField Matrix GlobalTheory.MirTower in

theorem mem_mirU_pred {K : Type} [Field K] {a : ℕ} (ha : 0 < a) (γ : GL (Fin a) K) :
    γ ∈ mirU K a (a - 1) ↔ ∀ j, γ.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ j =
      if j = ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩ then 1 else 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
  exact mem_mirU_last

open NumberField Matrix GlobalTheory.MirTower in

theorem lintegral_theta_unfold : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  intro E _ _ a ha μ _ 𝓕 𝓕P h𝓕 h𝓕P F hm hF
  set l : Fin a := ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩
  have hv : (Pi.single l 1 : Fin a → E) ≠ 0 := fun h0 => by simpa using congrFun h0 l
  have hP' : ∀ γ : GL (Fin a) E, γ ∈ mirU E a (a - 1) ↔ (Pi.single l 1 : Fin a → E) ᵥ* γ.val = Pi.single l 1 :=
    fun γ => by
      rw [mem_mirU_pred ha, Matrix.single_one_vecMul, funext_iff]
      simp only [Pi.single_apply, Matrix.row]
      rfl
  have he : algebraMap E (Ad E) ∘ (Pi.single l 1 : Fin a → E) = (Pi.single l 1 : Fin a → Ad E) := by
    funext j
    simp only [Function.comp_apply, Pi.single_apply]
    split_ifs <;> simp
  have := lintegral_tsum_vecMul μ hv hP' h𝓕 h𝓕P F hF (hm _).aemeasurable
  simp only [he, Matrix.single_one_vecMul] at this
  exact this

end GlobalTheory.ThetaUnfold
