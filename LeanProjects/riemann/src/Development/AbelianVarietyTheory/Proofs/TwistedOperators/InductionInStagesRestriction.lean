import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem restr_mem_indFun_stage : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  intro n a b ε W W' U _ _ τ s' y hs F hF g
  rw [mem_indFun_top] at hF
  obtain ⟨hc, hlaw⟩ := hF
  refine ⟨?_, fun g' hg' => restr_of_not_mem F g hg', ?_⟩
  · exact ((hc.comp (continuous_mul_const g)).continuousOn).congr fun m hm => restr_of_mem F g hm
  · intro u hu m hm x t ht h1 h2 h3 g' hg'
    have hM : u * m * t * g' ∈ leviOne ε W :=
      (leviOne ε W).mul_mem ((leviOne ε W).mul_mem ((leviOne ε W).mul_mem h1 h2) h3) hg'
    rw [restr_of_mem F g hM, restr_of_mem F g hg', mul_assoc (u * m * t) g' g, hlaw u hu m hm x t ht]
    congr 2
    have e : ∀ s r : Fin b → ℂ, pairing (fun _ => 1) (s + r) x =
        pairing (fun _ => 1) s x + pairing (fun _ => 1) r x := by
      intro s r
      simp only [pairing, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [e, e, hs x t ht h3]

end GlobalTheory.RealInd.Stages
