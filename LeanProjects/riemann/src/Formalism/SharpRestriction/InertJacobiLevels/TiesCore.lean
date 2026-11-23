import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.Inhab.GC

structure GHost (R : Ranks) where
  TT : Finset (R.A)
  T2 : Finset ℕ
  u0 : R.A
  cls : ℕ → PrimeClass

structure GD where
  R : Ranks
  host : GHost R
  hPf : ℕ → R.A

structure GParameters (D : GD) where
  sc : Scale
  Sc : ℝ
  etaSz : ℝ

def GParameters.lifts (D : GD) : Finset ℕ := Finset.Icc 1 D.R.m

abbrev HH (D : GD) : Type := D.R.A

def cG {D : GD} (L : GParameters D) : ℝ := 4 * L.Sc

def Nm (D : GD) : ℝ := (D.R.N D.R.m : ℝ)

def L1 (D : GD) (s : Scale) (p : ℕ) : ℕ := ⌈Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊

def L2 (D : GD) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D s p}

def Nstar (D : GD) (s : Scale) : ℝ := 2 * (D.R.n : ℝ) * s.delta1

def rho (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * (N1 s : ℝ) * La K s / D.R.k

def rhoB (D : GD) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * K.CN * Real.log s.x * La K s / D.R.k

def InBand0 (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rho D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rho D K s)

def InBand (D : GD) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rhoB D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rhoB D K s)

def c0num {D : GD} (L : GParameters D) : ℝ := 2 * L.sc.b' + 2 * cG L

def hP (D : GD) (p : ℕ) : HH D := D.hPf p

abbrev IsResidueClassZero (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.inertClass

abbrev IsSg (D : GD) (p : ℕ) : Prop := D.host.cls p = PrimeClass.signal

def partner (D : GD) (p : ℕ) (t : HH D) (e : ℕ) : Bool × HH D :=
  (decide (IsSg D p ∧ Odd e), t + e • hP D p)

def IsTopPl (D : GD) (z : Bool × HH D) : Prop := z.1 = false ∧ z.2 ∈ D.host.TT

def IsThickPl (D : GD) (z : Bool × HH D) : Prop :=
  z.1 = true ∧ z.2 ∈ D.host.T2.image (fun s : ℕ => D.R.dig s + D.host.u0)

def IsThinPl (D : GD) (z : Bool × HH D) : Prop := ¬ IsTopPl D z ∧ ¬ IsThickPl D z

structure Inst (D : GD) (L : GParameters D) where
  bs : HH D → HH D → HH D
  bs_orb : ∀ h t, ∃ i : ℕ, bs h t + i • h = t
  bs_step : ∀ h t, bs h (t + h) = bs h t
  off : ℕ → Bool × HH D → ℝ
  off_top : ∀ j z, IsTopPl D z → L.sc.b' / L.sc.x ≤ off j z ∧ off j z ≤ L.sc.b' / L.sc.x + L.etaSz
  off_thin : ∀ j z, IsThinPl D z → L.sc.w'' D.R.n ≤ off j z ∧ off j z ≤ L.sc.w'' D.R.n + L.etaSz
  off_thick : ∀ j z, IsThickPl D z → L.sc.b ≤ off j z ∧ off j z ≤ L.sc.b + L.etaSz + 1
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

variable {D : GD} {L : GParameters D}

def fill (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ :=
  (if z.1 = false ∧ z.2 ∈ D.host.TT then (b z.2 : ℝ) else 0) + X.off j z

def kaJ (D : GD) (j : ℕ) : ℝ := ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2

def fillG (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ := fill X b j z - kaJ D j

def stepP (D : GD) (p : ℕ) : HH D := if IsSg D p then 2 • hP D p else hP D p

def nP (D : GD) (p : ℕ) : ℕ :=
  if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p)

def reps (X : Inst D L) (p : ℕ) : Finset (HH D) := Finset.univ.image (X.bs (stepP D p))

def topsOn (X : Inst D L) (p : ℕ) (t0 : HH D) : Finset (HH D) :=
  D.host.TT.filter (fun t => X.bs (stepP D p) t = t0)

def Nv (X : Inst D L) (p : ℕ) (t0 : HH D) : ℕ := (topsOn X p t0).card

def topsPos (D : GD) (p : ℕ) (t0 : HH D) : Finset (Fin (addOrderOf (hP D p))) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • hP D p ∈ D.host.TT)

def wPos (D : GD) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) : Fin (addOrderOf (hP D p)) → ℤ :=
  fun i => a (t0 + (i : ℕ) • hP D p)

def IsV (X : Inst D L) (p : ℕ) (t : HH D) : Prop :=
  ∃ i : ℕ, i < nP D p ∧ Even i ∧ X.bs (stepP D p) t + i • hP D p = t

def Good (_X : Inst D L) (p : ℕ) (t0 : HH D) : Prop :=
  IsGoodOrbit (addOrderOf (hP D p)) (topsPos D p t0) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

def DIIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L +
      (rG L.sc : ℝ) * NplusF L.sc n' * c0num L⌉₊

def DIf (K : Consts) (L : GParameters D) (p n' : ℕ) : ℕ :=
  ⌈K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
      Real.logb p L.sc.a⌉₊

def tIIf (K : Consts) (L : GParameters D) (p n' N : ℕ) : ℝ :=
  K.tII * (rG L.sc : ℝ) * (N : ℝ) * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
    L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) + c0num L + (D.R.k : ℝ) * Qp L.sc p) +
    2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L

def kapIIf (K : Consts) (L : GParameters D) (N : ℕ) : ℝ :=
  min 1 (K.kII * (N : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A))

def c6f (K : Consts) (L : GParameters D) (p n' : ℕ) : ℝ :=
  8 * ((DIf K L p n' : ℝ) + 1) + K.kappaThresholdTwo * NplusF L.sc n' * (D.R.k : ℝ) * Real.logb p L.sc.a +
    4 * NplusF L.sc n' * cG L + 2 * (n' : ℝ) * cG L

open Classical in
def tIf (K : Consts) (L : GParameters D) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      (if dMinus TT y = 0 then 0 else
        min (b y : ℝ) ((a (posAdd y (n' - dMinus TT y)) : ℝ) / (p : ℝ) ^ dMinus TT y))) +
    K.kappaThresholdOne * (TT.card : ℝ) * (N1 L.sc : ℝ) *
      (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) +
    K.kappaThresholdTwo * (TT.card : ℝ) * (Qp L.sc p * c6f K L p n' +
      (D.R.k : ℝ) * Qp L.sc p +
      (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) + 2 * (n' : ℝ) * cG L

def kapLoc (X : Inst D L) (K : Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then kapIIf K L TT.card else X.kapI p n' TT a b

def al (L : GParameters D) (a : HH D → ℤ) (s : HH D) : ℝ := (a s : ℝ) - 2 * cG L

def capU (X : Inst D L) (b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  fillG X b j (partner D p s e) + cG L

def IsDist (D : GD) (p : ℕ) (s s' : HH D) (e : ℕ) : Prop :=
  0 < e ∧ partner D p s e = (false, s') ∧ ∀ e', 0 < e' → e' < e → partner D p s e' ≠ (false, s')

def Excl (D : GD) (p : ℕ) (s : HH D) (e : ℕ) : Prop :=
  Odd e ∧ ∃ s' ∈ D.host.TT, s' ≠ s ∧ IsDist D p s s' e

def dl (X : Inst D L) (K : Consts) (p : ℕ) (t0 : HH D) : ℝ :=
  K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
    K.dl2 * (Nv X p t0 : ℝ) * Real.logb p (2 * L.sc.a) ^ 2

open Classical in
def g0 (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  (∑ s ∈ topsOn X p t0, ∑' e : ℕ,
    if Odd e ∧ ¬ Excl D p s e then max 0 (al L a s / (p : ℝ) ^ e - capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def gU (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  gam p * (∑ s ∈ topsOn X p t0, al L a s) -
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), ∑' e : ℕ,
      if Odd e then min (al L a s / (p : ℝ) ^ e) (capU X b p j s e) else 0) -
    dl X K p t0

open Classical in
def Pr (X : Inst D L) (K : Consts) (b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : ℝ :=
  if L.sc.p0 D.R.k ≤ (p : ℝ) then
    (∑ s ∈ (topsOn X p t0).filter (fun s => ¬ IsV X p s), (fillG X b j (false, s) - (b s : ℝ))) +
      K.Pr1 * (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)
  else (rG L.sc : ℝ) * ((Nv X p t0 : ℝ) * (2 * L.sc.b' + cG L) +
      (nP D p : ℝ) * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D))

def Dp (K : Consts) (L : GParameters D) (p : ℕ) : ℕ :=
  if (p : ℝ) < L.sc.p0 D.R.k then DIIf K L p (nP D p) else DIf K L p (nP D p)

def tv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then tIIf K L p (nP D p) (Nv X p t0)
  else tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def kapv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def Cand (D : GD) (L : GParameters D) (K : Consts) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℝ) < L.sc.X' ∧ IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) ∧
    (L.sc.p0 D.R.k ≤ (p : ℝ) → ¬ InBand D K L.sc p)

open Classical in
def goodReps (X : Inst D L) (p : ℕ) : Finset (HH D) := (reps X p).filter (fun t0 => Good X p t0)

def Sig (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, kapv X K a b p t0

open Classical in
def VV (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) then goodReps X p else ∅

def Sv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  (⌈∑ j ∈ GParameters.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0)⌉ : ℤ)

open Classical in
def tauP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if VV X K a b p = ∅ then 0 else
    (X.ep p : ℝ) + ∑ t0 ∈ VV X K a b p,
      (D.R.m : ℝ) * ((⌈tv X K a b p t0⌉₊ : ℝ) + (Dp K L p : ℝ) + 1)

open Classical in
def ioP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  if h : (VV X K a b p).Nonempty then
    2 * Sig X K a b p * (VV X K a b p).sup' h (fun t0 => Sv X K a b p t0)
  else 0

open Classical in
def gainP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p j : ℕ) : ℝ :=
  if (IsResidueClassZero D p ∧ hP D p = 0) ∨ L.sc.X'' D.R.n < (p : ℝ) then 0 else
    (∑ t0 ∈ VV X K a b p, max (gU X K a b p j t0 - Pr X K b p j t0) (max (g0 X K a b p j t0) 0)) +
    ∑ t0 ∈ reps X p \ VV X K a b p, max (g0 X K a b p j t0) 0

open Classical in
def TTP (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if IsSg D p ∨ L.sc.X' ≤ (p : ℝ) then D.host.TT
  else D.host.TT.filter (fun t => X.bs (stepP D p) t ∈ VV X K a b p)

end Formalism.MainNotions.Inhab.GC

end
