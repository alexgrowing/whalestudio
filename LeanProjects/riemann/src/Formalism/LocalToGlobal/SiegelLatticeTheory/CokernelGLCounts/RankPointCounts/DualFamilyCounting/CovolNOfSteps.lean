import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolumeExponent

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped ENNReal

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LtPair (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev CIdx (r k : ℕ) : Type :=
  ((LtPair r × Bool) ⊕ (Fin r × Bool)) ⊕ ((Fin r × Fin k × Bool) ⊕ ((LtPair r × Bool) ⊕ Fin r))

def reim (c : ℂ) (t : Bool) : ℝ := if t then c.im else c.re

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def kapV (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) : CIdx D.R.rS D.R.k → ℝ := fun i =>
  match i with
  | Sum.inl (Sum.inl (p, t)) => reim (xMat X v s p.1.1 p.1.2) t
  | Sum.inl (Sum.inr (b, t)) => reim (yVec X u v s b) t
  | Sum.inr (Sum.inl (b, j, t)) => reim (phiMat X u v s b j) t
  | Sum.inr (Sum.inr (Sum.inl (p, t))) =>
      reim ((mMat X v s p.1.1 p.1.2 - star (mMat X v s p.1.2 p.1.1)) / 2) t
  | Sum.inr (Sum.inr (Sum.inr a)) => (mMat X v s a a).im

def kap (s : X.B.I.Ginf) : InfinitePlace X.B.I.F × CIdx D.R.rS D.R.k → ℝ := fun i => kapV X u i.1 s i.2

def twoU : ℝ := (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * (D.R.rS + 1) / 2))

def CoordMeas : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    Measurable (kap X u) ∧ MeasurableSet (X.NinfU u) ∧ Set.InjOn (kap X u) (X.NinfU u)

def CoordHaar : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (μ : Measure X.B.I.Ginf),
    IsHaarOnSet X.B.I (X.NinfU u) μ → μ.map (kap X u) = μ (boxN X u) • volume

def CoordCovol : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (FdN : Set X.B.I.Ginf),
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN →
    MeasurableSet (kap X u '' (FdN ∩ X.NinfU u)) ∧
      volume (kap X u '' (FdN ∩ X.NinfU u)) = ENNReal.ofReal (covolN X u / twoU X)

end Formalism.L2.SG.Pf.LsNc5
