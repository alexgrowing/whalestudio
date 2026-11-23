import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicProductOperator
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
theorem _root_.GlobalTheory.T.exists_adelic_product_operator : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (A : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (B : ((ι → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((ι → FiniteAdeleRing (𝓞 F) F) → ℂ)),
    ∃ H : ((ι → AF F) → ℂ) →ₗ[ℂ] ((ι → AF F) → ℂ),
      ∀ (f : SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ) (g : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ),
        H (pureA F f g) = pureA F (A f) (B g) := by
  first | exact @GlobalTheory.TensorGlue.exists_pure_operator | exact GlobalTheory.TensorGlue.exists_pure_operator | (intros; apply GlobalTheory.TensorGlue.exists_pure_operator <;> assumption)
