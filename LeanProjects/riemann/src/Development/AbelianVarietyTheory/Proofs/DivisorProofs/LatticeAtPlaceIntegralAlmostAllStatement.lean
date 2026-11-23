import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAtPlaceIntegralAlmostAll
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_at_place_integral_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ᶠ v in Filter.cofinite, ∀ l, l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ↔
      ∀ i, l.1 i ∈ v.adicCompletionIntegers F ∧ l.2 i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatIntegral.locCo_latAtV_eventually | exact GlobalTheory.LatIntegral.locCo_latAtV_eventually | (intros; apply GlobalTheory.LatIntegral.locCo_latAtV_eventually <;> assumption)
