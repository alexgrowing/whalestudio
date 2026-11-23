import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPartialFourierSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixXChar GlobalTheory.DblEval
open GlobalTheory.Doubling (absE)

open scoped Classical
attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_partial_fourier_surjective : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ A : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
      Function.Surjective A ∧
      (∀ z : κ ⊕ κ → mixedEmbedding.mixedSpace F, ∃ x y : κ → mixedEmbedding.mixedSpace F,
        ∀ f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ, ∃ f₁ : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
          (∀ u, f₁ u = Complex.exp (-(2 * Real.pi * Complex.I) *
              ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ z) : ℝ) : ℂ)) * f u) ∧
          ∀ u, A f₁ u = Complex.exp (-(2 * Real.pi * Complex.I) *
              ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (u ⬝ᵥ Sum.elim y (-y)) : ℝ) : ℂ)) * A f (u + Sum.elim x x)) ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ,
        SchwartzMap.integralCLM ℂ (MeasureTheory.volume : Measure (GlobalTheory.DiagForm.Vi F κ)) (GlobalTheory.DiagForm.compD F κ (A f)) = C * f 0 := by
  first | exact @GlobalTheory.diagHeis_archFourier | exact GlobalTheory.diagHeis_archFourier | (intros; apply GlobalTheory.diagHeis_archFourier <;> assumption)
