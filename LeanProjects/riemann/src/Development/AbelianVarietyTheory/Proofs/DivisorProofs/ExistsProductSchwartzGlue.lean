import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeIncInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.SchwartzProd

open scoped Classical in

theorem exists_prod : ∀ {F : Type} [Field F] [NumberField F] {n d d₁ : ℕ} (h : d = d₁ + 2) (G : SInf F (Fin n × Fin 2))
    (f : SInf F (Fin n × Fin d₁)), ∃ g : SInf F (Fin n × Fin d), ∀ y,
      g y = G (fun p => y ((idx h).symm (Sum.inr p))) * f (fun q => y ((idx h).symm (Sum.inl q))) := by
  intro F _ _ n d d₁ h G f
  obtain ⟨b, hb⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box f G
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n × Fin d => mixedEmbedding.mixedSpace F)
      (idx h).symm).symm b, fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hb, mul_comm]
  rfl

end GlobalTheory.ThK.EvAt0.SchwartzProd
