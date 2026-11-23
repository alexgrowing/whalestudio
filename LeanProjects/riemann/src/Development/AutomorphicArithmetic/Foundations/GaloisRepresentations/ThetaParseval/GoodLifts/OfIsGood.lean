import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.TP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

structure GoodNG (B : Base F E) : Prop where
  cm : IsCMExt F E σ
  unram : Algebra.Unramified (𝓞 F) (𝓞 E)
  std : IsStd B.ψ
  inert : ∀ v w, Formalism.UG.IsInertAt F E v w → (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧ PsiUnr B.ψ v
  psiP : ∀ v ∈ B.P, PsiUnr B.ψ v

end UpperTheory.TP

end
