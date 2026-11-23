import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumParabolicQuotientFubini
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusLeviMaximalCompactOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactParabolicUnipotentEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absHalf_eq_deltaHalf {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) :
    absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) =
      (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
        (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := GlobalTheory.T.modulus_half_levi_abs_det E a b w m

theorem hint_eq_level {H : Type} [Group H] (K L : Subgroup H) (u : H → ℂ) (hLK : L ≤ K) (hLu : L ≤ rStab u)
    (hfin : L.relIndex K ≠ 0) : hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out :=
  GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum H K L u hLK hLu hfin

theorem deltaHalf_eq_one {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) (h1 : m.1 ∈ GlobalTheory.LFun.KGL w a) (h2 : m.2 ∈ GlobalTheory.LFun.KGL w b) :
    GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
                 (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) = 1 := GlobalTheory.T.modulus_levi_maximal_compact_one E a b w m h1 h2

theorem int_points {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    ((GlobalTheory.LFun.KGL w n).subgroupOf (parB h w)).comap (uN h w) = intMat a b w ∧
      ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (sM h w) ≤ (GlobalTheory.LFun.KGL w n).subgroupOf (parB h w) :=
  GlobalTheory.T.maximal_compact_parabolic_unipotent_eq E a b n h w

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.LeviFubini

namespace GlobalTheory.LeviFubini

end GlobalTheory.LeviFubini
