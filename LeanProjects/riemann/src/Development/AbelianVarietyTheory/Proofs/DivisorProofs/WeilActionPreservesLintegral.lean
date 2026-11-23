import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ArchimedeanActsL2

theorem acts_lintegral_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n)
    (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), M.IsWeil ψ χX χW om →
    ∀ (x : UA σ X.J × UA σ W.J) (f f₁ : SInf F (Fin n × Fin d)), Acts (evI F) (om x) (⇑f) (⇑f₁) →
      ∀ μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure →
        ∫⁻ y, ‖f₁ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW x f f₁ hA μ hμ
  let g : (Fin n × Fin d → Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1
  have hg : g ∈ SB (Fin n × Fin d → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg0 : g 0 ≠ 0 := by
    show (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator (1 : (Fin n × Fin d → Af F) → ℂ) 0 ≠ 0
    rw [Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]
    exact one_ne_zero
  obtain ⟨μA, hμA, c, hc0, hct, hc⟩ := GlobalTheory.ArchimedeanUnitaryL2.exists_haar F _ μ g hg hg0
  let r : (Fin n × Fin d → AF F) → ℂ := fun x => g fun i => (x i).2
  have hS : ∀ f' : SInf F (Fin n × Fin d), tens (evI F) (⇑f') r ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f' => Submodule.subset_span ⟨f', g, hg, rfl⟩
  have hr : ∀ x z, At (evI F) z → r (x + z) = r x := by
    intro x z hz
    refine congrArg g (funext fun i => ?_)
    show (x i).2 + (z i).2 = (x i).2
    rw [GlobalTheory.ArchimedeanUnitaryL2.snd_eq_zero hz i, add_zero]
  have hU := (IsUWeilPair.isUSplitting hW).unit μA hμA x (tens (evI F) (⇑f) r) (hS f)
  have hAct : om x (tens (evI F) (⇑f) r) = tens (evI F) (⇑f₁) r := hA r ⟨hr, hS f⟩
  rw [hAct] at hU
  have h1 := ((hc f₁).symm.trans hU).trans (hc f)
  exact (ENNReal.mul_right_inj hc0 hct).1 h1

end GlobalTheory.ArchimedeanActsL2
