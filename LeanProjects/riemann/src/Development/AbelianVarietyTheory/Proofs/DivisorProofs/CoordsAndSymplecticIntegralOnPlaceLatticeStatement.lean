import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsAndSymplecticIntegralOnPlaceLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_and_symplectic_integral_on_placeLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) (ξ : E) (v : HeightOneSpectrum (𝓞 F))
    (co : (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F),
    (∀ x, co (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k))) →
    (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) →
    (∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (GlobalTheory.WeilM.symp σ ξ JX JY t t') ∈ v.adicCompletionIntegers F) →
    ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t},
      (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).1 k) ∧ evFin F v ((co γ).1 k) ∈ v.adicCompletionIntegers F ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).2 k) ∧ evFin F v ((co γ).2 k) ∈ v.adicCompletionIntegers F) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∧
        evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∈ v.adicCompletionIntegers F) := by
  first | exact @GlobalTheory.LatticeAtPlace.coords_symp_integral | exact GlobalTheory.LatticeAtPlace.coords_symp_integral | (intros; apply GlobalTheory.LatticeAtPlace.coords_symp_integral <;> assumption)
