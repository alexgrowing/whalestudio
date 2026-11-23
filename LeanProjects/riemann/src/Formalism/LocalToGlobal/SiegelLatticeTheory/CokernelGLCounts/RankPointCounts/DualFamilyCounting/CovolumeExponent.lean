import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def eV (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.eR a)
def fV (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.fR a)
def zV (v : InfinitePlace X.B.I.F) : Fin X.B.I.n → ℂ := rv X.B.I v (X.zR u)

def xMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ eV X v a)

def yVec (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Fin D.R.rS → ℂ :=
  fun b => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ zV X u v)

def phiMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.k) ℂ :=
  fun b j => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ X.wfr u v j)

def aMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  fun b a => hJ (X.B.I.ε v) (fV X v b) (uMat (s v) *ᵥ fV X v a)

def mMat (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : Matrix (Fin D.R.rS) (Fin D.R.rS) ℂ :=
  (xMat X v s)⁻¹ * aMat X v s

def InUnit (t : ℝ) : Prop := 0 ≤ t ∧ t < 1

def InBox (c : ℂ) : Prop := InUnit c.re ∧ InUnit c.im

def boxN : Set X.B.I.Ginf :=
  X.NinfU u ∩ {s | ∀ v,
    (∀ b a : Fin D.R.rS, b < a → InBox (xMat X v s b a)) ∧ (∀ b, InBox (yVec X u v s b)) ∧
    (∀ b j, InBox (phiMat X u v s b j)) ∧
    (∀ b a : Fin D.R.rS, b < a → InBox ((mMat X v s b a - star (mMat X v s a b)) / 2)) ∧
    ∀ a, InUnit (mMat X v s a a).im}

def covolumeExponent (r k : ℕ) : ℝ := -((8 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 6 * (k : ℝ) * (r : ℝ) ^ 2 + r) / 6)

def covolN : ℝ :=
  (((D.mem u).A.T : ℕ) : ℝ) ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
    (2 : ℝ) ^ (-((Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS * (D.R.rS - 1) / 2) : ℕ) : ℝ)) *
    |(NumberField.discr X.B.I.F : ℝ)| ^ covolumeExponent D.R.rS D.R.k

def CovolN : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ : Measure X.B.I.Ginf) (FdN : Set X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    μ FdN = ENNReal.ofReal (covolN X u /
      (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * (D.R.rS + 1) / 2))) * μ (boxN X u)

end Formalism.L2.SG.Pf.LsNc5
