import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem errXS_pi_of_colT : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  intro B f T w Z t
  have hc : t.full.1.cols = t.C.herm := t.full.2
  refine ⟨?_, ?_⟩
  · show (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← t.C.piG]
    exact (t.std _).gl.piG
  · funext u
    show (t.full.1.cols.atT u).piU = _
    rw [hc, ← t.C.piU u]
    exact (t.std u).piU

end GlobalTheory.Svd
