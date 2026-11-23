import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

structure HostNum (D : D7) (L : SizeData₂ D) (PP A M : ℝ) : Prop where
  big : M ≤ L.sc.L ∧ 10 ≤ L.sc.L ∧ L.sc.L ≤ L.sc.x ∧ 1 ≤ Real.log (Real.log L.sc.x)
  f8 : 8 ≤ D.R.f
  deg : Module.finrank ℚ D.host.E = 2 * D.R.f
  logfr : Real.log ((D.R.f : ℝ) * D.R.r) ≤ L.sc.L ∧ Real.log (D.R.nV : ℝ) ≤ L.sc.L
  logg : ∀ k, Real.log (D.host.g k : ℝ) ≤ 9 * L.sc.L + 1
  disc : Real.log |(discr D.host.E : ℝ)| ≤ 4 * D.R.f * L.sc.L
  logd : Real.log (D.host.d : ℝ) ≤ L.sc.L
  split : 5 ≤ D.host.splitBound
  cop : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)
  ppLow : zBase L ^ 12 ≤ PP
  poly : 1 ≤ A ∧ PP ≤ L.sc.x ^ A ∧ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L ≤ L.sc.x ^ A
  room : (L.sc.x ^ A) ^ M ≤ L.sc.b
  low : Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n

def wtsAt (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) :
    GlobalTheory.MeanTop.Wts (Psi p.T.Q.H) ((dat p i).p + (dat p i).q) :=
  { kc := D.R.k - 1, p := (dat p i).p, T := lenT p i PP, Dd := dimFlag (dat p i), c0 := cZero D ((i : ℕ) + 1), h0 := h0, S := S,
    eta := eta, b := 4 * L.sc.b, w := fun τ => (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ), u := uW p i, u1 := u1 }

theorem quo_iff (PP : ℝ) (h0 : ℤ) (S eta : ℝ) (u1 : Weight (dat p i)) : Quo p i PP u1 ↔ (wtsAt p i PP h0 S eta u1).IsDiv :=
  Iff.rfl

structure WtNum (PP : ℝ) : Prop where
  sig : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 ∧ (dat p i).q = (D.R.sigW ((i : ℕ) + 1)).2 ∧ (dat p i).p + (dat p i).q = D.R.r
  card : Nat.card (Psi p.T.Q.H) = D.R.f
  dim : dimFlag (dat p i) = D.R.f * D.R.r.choose 2
  cols : (p.κ i).n = D.R.nV
  dom : Dom (wtA (p.κ i)) (p.κ i).n
  unit : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
  om : |(ofRecord D L p.Del p.h0).logOm| ≤ 3 * L.sc.L
  up : ∀ τ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ 4 * L.sc.b
  low : ∀ τ, L.sc.w'' D.R.n ≤ 2 * (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ)
  what₂ : PP ^ 2 * D.R.r * D.R.m * D.R.k * (dimFlag (dat p i) : ℝ) ^ 3 ≤ L.sc.b ∧
    PP * lenT p i PP * (dimFlag (dat p i) : ℝ) ^ 2 * L.sc.L ≤ L.sc.b
  hyp : (i : ℕ) + 1 < D.R.m → ∃ (h0 : ℤ) (S eta : ℝ), 0 ≤ S ∧ 0 ≤ eta ∧ PP * (S + eta) ≤ 100 * L.sc.w'' D.R.n ∧
    4 * (lenT p i PP : ℤ) ^ 2 ≤ h0 ∧
    PP * lenT p i PP * D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * dimFlag (dat p i) ≤ h0 ∧
    ∀ u1, (wtsAt p i PP h0 S eta u1).Hyp

def HostN (M : ℝ) : Prop := Lifts fun Fm x _ ι _ _ PP A => HostNum (Fm.D x ι) (Fm.L x ι) PP A M

def WtN : Prop := Lifts fun _ _ _ _ p i PP _ => WtNum p i PP

end GlobalTheory.CovTop

end
