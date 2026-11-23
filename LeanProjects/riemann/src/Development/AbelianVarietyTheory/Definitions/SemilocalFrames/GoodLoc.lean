import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

abbrev GT (Y : Full X) (u : D.what₂.Word) : Type := GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)

def trI (C : Choice X 1) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def gamT (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (τ : D.what₂.Tau) : MatKR D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (t.pt.1 (vOf X τ))

def covN (C : Choice X 1) (Y : Full X) (u : D.what₂.Word) : ℝ≥0∞ :=
  Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' Y.FN u)

def FundR {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (K : Set X.B.I.Ginf) : Prop :=
  MeasurableSet K ∧ ∀ x ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! q, q ∈ ROinf t ∧ q * x ∈ K

def phiV (C : Choice X 1) (τ : D.what₂.Tau) (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ :=
  C.Qi τ *ᵥ rv X.B.I (vOf X τ) (X.crd y)

def GoodLoc (C : Choice X 1) (hB : WuBessel C) : Prop :=
  LocFactor C ∧ ∀ u τ, GoodW D τ u u 1 (locW C u u τ) ∧ GoodS D (lamD D τ) (locS hB u u τ)

def LocDatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D), Nonempty D.what₂.Word → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.BasicNotions.dsigTie D →
    ∃ (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB
end GlobalTheory.TypeAsm
