import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NrmAbsOfValuationEqExp

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.NrmCompl

theorem isNrm_nrmAbs {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) : IsNrm P (nrmAbs P) := by
  intro x
  refine ⟨fun hx => (nrmAbs_eq_one_iff P (x : P.adicCompletion L)).2 hx, fun hx => ?_⟩
  have h : Valued.v (x : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := hx
  rw [nrmAbs_of_valuation_eq_exp P h, _root_.zpow_neg_one]
  rfl

theorem exists_isNrm : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)),
    ∃ nrm : AbsoluteValue (P.adicCompletion L) ℝ, IsNrm P nrm :=
  fun _ _ _ P => ⟨nrmAbs P, isNrm_nrmAbs P⟩

end GlobalTheory.Mem.NrmCompl
