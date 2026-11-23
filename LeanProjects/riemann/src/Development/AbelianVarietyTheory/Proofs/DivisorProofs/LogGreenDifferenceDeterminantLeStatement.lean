import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsLogGrNormSubLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_green_difference_determinant_le : HTBoundSt → ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}
    {s : FinalTheorems S κ} (fl : s.Flag) (k : s.Comp) (τ : D.host.E →+* ℂ) (T : Finset ℕ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : Ext v) (y : AlgPt (fl.C k).Y),
    |lgOf (fl.C k) (detSym S.Dw (ArIn.ind T) none τ) v ε y -
        lgOf (fl.C k) (detSym S.Dw (fun _ => false) none τ) v ε y| ≤
      if resP v ∈ T then |Real.log (ε.w (resP v)) / Real.log (resP v)| *
        (N * (Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff D.host.E (resP v) * Real.log (resP v))) else 0 := by
  first | exact @GlobalTheory.LgDiff.abs_lgOf_detSym_sub_le | exact GlobalTheory.LgDiff.abs_lgOf_detSym_sub_le | (intros; apply GlobalTheory.LgDiff.abs_lgOf_detSym_sub_le <;> assumption)
