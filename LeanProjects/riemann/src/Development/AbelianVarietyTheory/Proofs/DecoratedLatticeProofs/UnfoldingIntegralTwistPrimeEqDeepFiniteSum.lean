import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Formalism.LocalToGlobal.Columns.ChainTwAn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralPositionOneEqFiniteSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearWeilActionSupportAndPeriodIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegralStatement

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwSumAgree

theorem sumAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hAt
  have hPA := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hAt
  have hiL := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => GlobalTheory.StepData.plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) (fun _ _ _ => rfl)
  intro j c h a b g g' hag hbg' ha hb hD
  have hm := hAt.steps
  refine ⟨j + 1, j + 1, fun A' B' hA hB e' e hoe' hoe x => ?_⟩
  obtain ⟨E', hE', hg⟩ := id hag
  obtain ⟨E, hE, hg'⟩ := id hbg'
  have hj : j < R.m := by omega
  have hom := GlobalTheory.TwBridge.Model.om_agree Ch sel mu cst σ₀ P ι s W hAt hok j (c + 1) (c + 1 + 1) hj E' E a b g g' hg hg'
    ((W.T s R).Phi j (c + 1) (by omega)) (PhiAt Ch mu cst.sharp j P.1)
    (fun y => hPA.1 j (c + 1) (by omega) E' E hE' hE y)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl j (c + 1 + 1) a g hag ha
  obtain ⟨h1', h2'⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl (j + 1) (c + 1) b g' hbg' hb
  have hSP := GlobalTheory.T.linearWeilAction_support_and_period_integral W.ϖ ((W.unif W.ϖ).2 le_rfl) j ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega))
    (hiL.1 j (c + 1) (by omega)) (hiL.2.1 j (c + 1) (by omega)) g g' h1 h2 h1' h2'
  have hpsi : ∀ z, IntAt P.1 ((qOf P.1 : X.E) ^ (j + 1) * z) → (W.ψ (ι z) : ℂ) = σ₀ (cst.psi P z) :=
    fun z hz => hAt.psi z (twAn_qpow_mul (by omega) hz)
  have o1 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e' z).val) (R.N j)) E' := by
    rintro (z | z)
    · exact (hE' _).trans (hoe' z).symm
    · exact hE' _
  have o2 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e z).val) (R.N (j + 1))) E := by
    rintro (z | z)
    · exact (hE _).trans (hoe z).symm
    · exact hE _
  exact GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum X.E X.K k P.1 (qOf P.1) ι W.ϖ σ₀ W.ψ ν (cst.psi P) (j + 1) hAt.compl W.unif W.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    A' B' (by omega) (by unfold cOf; omega) (by unfold cOf; omega) hA hB e' e E' E o1 o2 _ _ _ hom hSP.1 hSP.2 x

end GlobalTheory.TwSumAgree
