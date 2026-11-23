import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def TruncatedKernelConvergence : Prop :=
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure], KernelConvergence Φ (levelAll D.sp.cm.sig V.gram L a) μ

example (D : D7) : wittIndex (CuspDecay.Model.plane D) = 1 ∧
    ∃ (Φ : WittFrame (CuspDecay.Model.plane D)) (L : _) (a : _), Φ.IsGood D.sp.cm L a :=
  ⟨wittIndex_plane D, exists_isGood _⟩

end GlobalTheory.Published

end
