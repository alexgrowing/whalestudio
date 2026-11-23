import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartialFourierBijective
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
theorem _root_.GlobalTheory.T.exists_finite_partial_fourier_bijective : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ],
    ∃ B : ((κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), B g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) ∧
      (∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), ∃ g' ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F), B g' = g) ∧
      (∀ z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F, ∃ x y : κ → FiniteAdeleRing (𝓞 F) F,
        ∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
          B (fun u => ψ (((0, u ⬝ᵥ z) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) * g u) =
            fun u => ψ (((0, u ⬝ᵥ Sum.elim y (-y)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) : AF F) *
              B g (u + Sum.elim x x)) ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F),
        ∫ v : κ → FiniteAdeleRing (𝓞 F) F, B g (Sum.elim v v) ∂Measure.addHaar = C * g 0 := by
  first | exact @GlobalTheory.PartialFourierFin.exists_partialFourier_diag | exact GlobalTheory.PartialFourierFin.exists_partialFourier_diag | (intros; apply GlobalTheory.PartialFourierFin.exists_partialFourier_diag <;> assumption)
