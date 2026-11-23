import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartTripleStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.ThK.InfB

theorem continuous_integral_of_bound {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {Y : Type} [MeasurableSpace Y]
    {μ : Measure Y} (Φ : SchwartzMap D ℂ → Y → ℂ) (hlin : ∀ φ ψ y, Φ (φ - ψ) y = Φ φ y - Φ ψ y)
    (s : Finset (ℕ × ℕ)) (C : ℝ) (h : Y → ℝ) (hh : Integrable h μ) (hm : ∀ φ, AEStronglyMeasurable (Φ φ) μ)
    (hb : ∀ φ y, ‖Φ φ y‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ D ℂ)) φ * h y) :
    Continuous fun φ => ∫ y, Φ φ y ∂μ := by
  have hi : ∀ φ, Integrable (Φ φ) μ := fun φ =>
    Integrable.mono' (hh.const_mul (C * (s.sup (schwartzSeminormFamily ℂ D ℂ)) φ)) (hm φ)
      (Eventually.of_forall fun y => hb φ y)
  set p := s.sup (schwartzSeminormFamily ℂ D ℂ) with hp
  have hpc : Continuous fun φ => p φ := by
    exact Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ D ℂ).continuous_seminorm i
  have key : ∀ φ ψ, ‖(∫ y, Φ φ y ∂μ) - ∫ y, Φ ψ y ∂μ‖ ≤ (C * ∫ y, h y ∂μ) * p (φ - ψ) := by
    intro φ ψ
    rw [← integral_sub (hi φ) (hi ψ)]
    have e : (fun y => Φ φ y - Φ ψ y) = Φ (φ - ψ) := funext fun y => (hlin φ ψ y).symm
    rw [e]
    calc ‖∫ y, Φ (φ - ψ) y ∂μ‖ ≤ ∫ y, C * p (φ - ψ) * h y ∂μ :=
          norm_integral_le_of_norm_le (hh.const_mul _) (Eventually.of_forall fun y => hb _ y)
      _ = (C * ∫ y, h y ∂μ) * p (φ - ψ) := by rw [integral_const_mul]; ring
  refine continuous_iff_continuousAt.2 fun φ₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun φ => (C * ∫ y, h y ∂μ) * p (φ - φ₀)) (𝓝 φ₀) (𝓝 0) := by
    have : Tendsto (fun φ => p (φ - φ₀)) (𝓝 φ₀) (𝓝 (p (φ₀ - φ₀))) :=
      (hpc.comp (continuous_id.sub continuous_const)).tendsto φ₀
    rw [sub_self, map_zero] at this
    simpa using this.const_mul (C * ∫ y, h y ∂μ)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun φ => key φ φ₀) ht

theorem coneFun_continuousOn : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ μ : Measure (idelesAt E (evI F)), μ.IsHaarMeasure → ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      ∀ f, ContinuousOn (GlobalTheory.ThK.InfB.coneFun B G.M' om' ei' μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l f)
        (UAt σ G.V' (evI F)) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ μ hμ l f
  obtain ⟨s, C, h, hh, hm, hb⟩ := GlobalTheory.T.config_B_local_part_triple hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hloc X om om' om₁ om₁' hT hT₁ μ hμ l
  have hψ := hT.base.std
  have hlin : ∀ (φ ψ : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (y : idelesAt E (evI F)),
      l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) (φ - ψ))) =
        l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) φ)) -
        l (((X.ν y.1 : ℂ) * ((absE F E y.1 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
          ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) ψ)) := by
    intro φ ψ y
    have hR : IsLinearMap ℂ (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' y.1))) :=
      ⟨fun f g => funext fun x => mul_add _ _ _, fun c f => funext fun x => mul_left_comm _ _ _⟩
    have e1 : φ - ψ = (1 : ℂ) • φ + (-1 : ℂ) • ψ := by rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e1, locOpInf_lin hR (fun g => ⟨_, (locOpInf_rho G.M'.co hψ (shiftB σ H H' y.1) g).1⟩), one_smul, neg_one_smul,
      ← sub_eq_add_neg, map_sub, smul_sub, map_sub]
  have hΨ := continuous_integral_of_bound _ hlin s C h hh hm hb
  exact hΨ.comp_continuousOn (GlobalTheory.T.local_weil_operator_continuous hP F E σ B a (b + 2) G X om om' hT f)

end GlobalTheory.ThK.InfB

end
