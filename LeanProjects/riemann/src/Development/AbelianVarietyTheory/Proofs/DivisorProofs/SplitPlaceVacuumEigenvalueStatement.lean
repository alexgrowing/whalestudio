import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceVacuumEigenvalue
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
theorem _root_.GlobalTheory.T.split_place_vacuum_eigenvalue : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ v (t : E →ₐ[F] Fv F v), GlobalTheory.PairVac.GoodPlace B M χX v →
      ∀ g ∈ GlobalTheory.InertSph.KAt σ W v, ∀ c : ℂ, Acts (evFin F v) (om (1, g)) (M.vac v) (c • M.vac v) → c = 1 := by
  first | exact @GlobalTheory.PairVacSplit.scalar_eq_one_split | exact GlobalTheory.PairVacSplit.scalar_eq_one_split | (intros; apply GlobalTheory.PairVacSplit.scalar_eq_one_split <;> assumption)
