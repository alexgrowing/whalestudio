import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := rank_base_space D.R
  simp only [Ranks.N, zero_mul, add_zero] at this
  omega

variable {D : D7} (X : HidaSetting D)

def ci : Fin (2 * D.R.rS + D.R.k + 1) ≃ Fin X.B.I.n := finCongr (X.n_eq.trans (rank_eq D)).symm

def crdH (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E := fun i => X.bas.repr y (ci X i)

def vecOf : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).toLinearMap

def Jc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E :=
  fun i j => (VS D).hT (X.bas (ci X i)) (X.bas (ci X j))

def Lc : Submodule (𝓞 D.host.E) (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :=
  (VS D).L0.comap ((vecOf X).restrictScalars (𝓞 D.host.E))

def Pc (u : D.what₂.Word) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i b => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.eX a) i) b

def fc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin D.R.rS) D.host.E :=
  Matrix.of fun i a => crdH X (X.fY a) i

def Tc (u : D.what₂.Word) : D.host.F := (((D.mem u).A.T : ℕ) : D.host.F)

def tauOf (D : D7) (w : InfinitePlace D.host.E) : D.what₂.Tau :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose

def Direct (D : D7) (w : InfinitePlace D.host.E) : Prop := w.embedding = embS D (tauOf D w)

def A0 {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  (C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix id (ci X)

def Ac {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  if Direct D w then A0 X C w else (A0 X C w).map star

def sc (D : D7) (a : Fin D.R.rS) : ℝ := (2 * D.host.v) ^ (D.R.rS - (a : ℕ))

def trX {θ : ℝ} (C : Choice X θ) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then M else fun i j => star (M i j)

def Gm (D : D7) (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun w => cjw D w (y (tauOf D w))

end GlobalTheory.CovDom
