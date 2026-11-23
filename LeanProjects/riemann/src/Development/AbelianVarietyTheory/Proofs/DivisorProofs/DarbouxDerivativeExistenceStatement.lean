import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDerivativeExistence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_derivative_existence : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → GlobalTheory.RealLift.DerEx →
    GlobalTheory.RealLift.ActsLaws → HasDH F κ ∧
      (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
        ActsD (evI F) (fun t => co.rho ψ (realAd F t • u)) f f₁ ↔ ⇑f₁ = dH (cw co u).1 (cw co u).2 ⇑f) ∧
      ∀ a b : κ → mixedEmbedding.mixedSpace F, ∃ u : Matrix α β (AE F E), At (evI F) u ∧ cw co u = (a, b) := by
  first | exact @GlobalTheory.ThK.PlaneEv.LineDer.derivLines | exact GlobalTheory.ThK.PlaneEv.LineDer.derivLines | (intros; apply GlobalTheory.ThK.PlaneEv.LineDer.derivLines <;> assumption)
