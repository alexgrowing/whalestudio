import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (φ : GlobalTheory.CuspRep.Sm E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k φ)) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => GlobalTheory.CuspRep.cptRep E a k (GlobalTheory.CuspRep.lie E a X φ))) := by
  first | exact @GlobalTheory.CuspRep.KFin.kfin_lie | exact GlobalTheory.CuspRep.KFin.kfin_lie | (intros; apply GlobalTheory.CuspRep.KFin.kfin_lie <;> assumption)
