import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField

def MtType {D : D7} (u : D.what₂.Word) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (i : ℕ) (h : i < D.R.m), (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ mt (i + 1) k ^ n = 1) ∧
    ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hcW u τ).e ⟨i, h⟩) ∧
      ∀ z : unitary D.host.E, ((mt (i + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, TaylorLogMetric.embT D τ (z : D.host.E) ^ e τ

def MtIs {D : D7} {C : Formalism.L2.Host.CharFrame D} (Dt : Formalism.L2.Host.DtTied D C) {nch : NChoice D}
    (Tp : Formalism.L2.Host.TupTied D C nch) (μ : D.what₂.Tup) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ (j : Fin D.R.m) a, Formalism.L2.Host.IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (Tp.tup μ j).1 a

end GlobalTheory.KerJ
