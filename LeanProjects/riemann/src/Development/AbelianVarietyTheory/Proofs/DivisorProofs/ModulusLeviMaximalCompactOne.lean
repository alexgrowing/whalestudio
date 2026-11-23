import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DeltaOneKGL

theorem deltaHalf_KGL_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), m.1 ∈ GlobalTheory.LFun.KGL w a → m.2 ∈ GlobalTheory.LFun.KGL w b → GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) = 1 := by
  intro E _ _ _ a b w m h1 h2
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hn : ∀ {n : ℕ} (k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n →
      GlobalTheory.SplitWeil.nabs (w.adicCompletion E) (Matrix.GeneralLinearGroup.det k) = 1 := by
    intro n k hk
    apply GlobalTheory.SmGL.nabs_eq_one
    rw [he.eq_one_iff_eq_one]
    exact GlobalTheory.BCT.AbsHalfInv.v_det_KGL hk
  rw [GlobalTheory.SmGL.deltaHalf_two]
  ext
  simp [GlobalTheory.SmGL.val_absPow, hn _ h1, hn _ h2]

end GlobalTheory.DeltaOneKGL
