import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTrueWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms

namespace GlobalTheory.Core.Cls

theorem errXS_pi_and_val : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (b : CoreB K w Z), (Formalism.L2.Herm.toErrXS b.t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS b.t.full.1).piT = w.px.piT ∧ Formalism.L2.Host.ValLL0 (w.D Z) (TC.cf w.I w.l Z) := by
  intro K B f T w Z b
  have hc : b.t.full.1.cols = b.t.C.herm := b.t.full.2
  refine ⟨?_, ?_, ?_⟩
  · show (b.t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← b.t.C.piG]
    exact (b.t.std _).gl.piG
  · funext u
    show (b.t.full.1.cols.atT u).piU = _
    rw [hc, ← b.t.C.piU u]
    exact (b.t.std u).piU
  · rcases w with ⟨px, I, ok, C_eq, S_eq, xi_range, pins, l, l0, δ, exact, fld, val⟩
    subst C_eq
    exact val _ _ _ _ _ _

end GlobalTheory.Core.Cls
