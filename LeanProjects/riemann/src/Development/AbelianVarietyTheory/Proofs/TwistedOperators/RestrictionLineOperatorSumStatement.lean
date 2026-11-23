import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_line_operator_sum : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ (m : ℕ) (f f₁ : Fin m → SInf F (Fin a × Fin (a + a')))
    (r : Fin m → (Fin a × Fin (a + a') → AF F) → ℂ), (∀ i, Rest (evI F) (⇑(f i)) (r i)) →
    (∀ i, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (⇑(f i)) (⇑(f₁ i))) →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, tens (evI F) (⇑(f i)) (r i)))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (∑ i, tens (evI F) (⇑(f₁ i)) (r i)))) 0 := by
  first | exact @GlobalTheory.ThetaLineDeriv.main | exact GlobalTheory.ThetaLineDeriv.main | (intros; apply GlobalTheory.ThetaLineDeriv.main <;> assumption)
