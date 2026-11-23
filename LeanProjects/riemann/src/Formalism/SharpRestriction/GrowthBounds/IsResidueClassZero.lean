import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataGatTies
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.GrowthBounds.DataGChain

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

structure Consts where
  La : ℝ
  rho : ℝ
  kII : ℝ
  tII : ℝ
  DII : ℝ
  szII : ℝ
  kII' : ℝ
  DI : ℝ
  kappaThresholdOne : ℝ
  kappaThresholdTwo : ℝ
  kI : ℝ
  dl1 : ℝ
  dl2 : ℝ
  Pr1 : ℝ
  CN : ℝ

def Consts.Nonneg (K : Consts) : Prop :=
  0 ≤ K.La ∧ 0 ≤ K.rho ∧ 0 ≤ K.kII ∧ 0 ≤ K.tII ∧ 0 ≤ K.DII ∧ 0 ≤ K.szII ∧ 0 ≤ K.kII' ∧ 0 ≤ K.DI ∧
    0 ≤ K.kappaThresholdOne ∧ 0 ≤ K.kappaThresholdTwo ∧ 0 ≤ K.kI ∧ 0 ≤ K.dl1 ∧ 0 ≤ K.dl2 ∧ 0 ≤ K.Pr1 ∧ 0 ≤ K.CN

abbrev HH (D : D7) : Type := D.R.A

def hG (s : Scale) : ℝ := 2 + 8 * s.eps

def KG (s : Scale) : ℕ := ⌈8 * (hG s + 2) / s.eps⌉₊

def rG (s : Scale) : ℕ := KG s + 1

def N1 (s : Scale) : ℕ := orbitWindowCount (rG s) s.delta1 (hG s) s.x

def Gp (s : Scale) : ℕ := goodG' (rG s) s.delta1 (hG s) s.x

def cG {D : D7} (L : SizeData₂ D) : ℝ := 4 * L.Sc

def Nm (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

def L1 (D : D7) (s : Scale) (p : ℕ) : ℕ := ⌈Real.logb p (((D.R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊

def L2 (D : D7) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D s p}

def Nstar (D : D7) (s : Scale) : ℝ := 2 * (D.R.n : ℝ) * s.delta1

def La (K : Consts) (s : Scale) : ℝ := K.La * (N1 s : ℝ) ^ 2 * Real.log s.a

def rho (D : D7) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * (N1 s : ℝ) * La K s / D.R.k

def rhoB (D : D7) (K : Consts) (s : Scale) : ℝ :=
  4 * Nstar D s * s.x ^ s.eps * La K s / D.R.k + K.rho * K.CN * Real.log s.x * La K s / D.R.k

def CbLarge (K : Consts) (s : Scale) : Prop := (N1 s : ℝ) ≤ K.CN * Real.log s.x

theorem rho_le_rhoB (D : D7) (K : Consts) (s : Scale) (hr : 0 ≤ K.rho) (hLa : 0 ≤ La K s) (h : CbLarge K s) :
    rho D K s ≤ rhoB D K s := by
  unfold rho rhoB
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h1 : K.rho * (N1 s : ℝ) * La K s ≤ K.rho * (K.CN * Real.log s.x) * La K s := by
    apply mul_le_mul_of_nonneg_right _ hLa
    exact mul_le_mul_of_nonneg_left h hr
  have h2 := div_le_div_of_nonneg_right h1 hk
  rw [show K.rho * K.CN * Real.log s.x * La K s = K.rho * (K.CN * Real.log s.x) * La K s by ring]
  linarith [h2]

def InBand0 (D : D7) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rho D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rho D K s)

def InBand (D : D7) (K : Consts) (s : Scale) (p : ℕ) : Prop :=
  s.p0 D.R.k ≤ (p : ℝ) ∧ (p : ℝ) < s.X' ∧ ∃ d : ℕ, 1 ≤ d ∧
    s.X' * (1 - rhoB D K s) ≤ (p : ℝ) ^ d ∧ (p : ℝ) ^ d ≤ s.X' * (1 + rhoB D K s)

def Qp (s : Scale) (p : ℕ) : ℝ := (p : ℝ) ^ (Gp s)

def gam (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) ^ 2 - 1)

def c0num {D : D7} (L : SizeData₂ D) : ℝ := 2 * L.sc.b' + 2 * cG L

def frobSet (D : D7) (p : ℕ) : Set (D.R.GG) :=
  {g | ∃ (P : Ideal (𝓞 D.host.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P ∧ D.host.galE σ = g}

def hP (D : D7) (p : ℕ) : HH D :=
  D.R.iotaInv (Classical.epsilon (fun g => g ∈ frobSet D p)).2

abbrev IsResidueClassZero (D : D7) (p : ℕ) : Prop := D.host.cls p = PrimeClass.inertClass

abbrev IsSg (D : D7) (p : ℕ) : Prop := D.host.cls p = PrimeClass.signal

def HEv (D : D7) (p : ℕ) : Prop := Even (addOrderOf (hP D p))

def IsCs (D : D7) (p : ℕ) : Prop := IsResidueClassZero D p ∧ Odd (addOrderOf (hP D p)) ∧ hP D p ≠ 0

theorem HEv.ne_zero {D : D7} {p : ℕ} (h : HEv D p) : hP D p ≠ 0 := by
  intro h0
  unfold HEv at h
  rw [h0, addOrderOf_zero] at h
  exact Nat.not_even_one h

theorem HEv.not_isCs {D : D7} {p : ℕ} (h : HEv D p) : ¬ IsCs D p := fun hc => Nat.not_even_iff_odd.mpr hc.2.1 h

theorem class_zero_trichotomy {D : D7} {p : ℕ} (h : IsResidueClassZero D p) : HEv D p ∨ hP D p = 0 ∨ IsCs D p := by
  by_cases he : Even (addOrderOf (hP D p))
  · exact Or.inl he
  · by_cases h0 : hP D p = 0
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr ⟨h, Nat.not_even_iff_odd.mp he, h0⟩)

theorem IsCs.three_le {D : D7} {p : ℕ} (h : IsCs D p) : 3 ≤ addOrderOf (hP D p) := by
  obtain ⟨-, hodd, hne⟩ := h
  have h1 : addOrderOf (hP D p) ≠ 1 := fun h1 => hne (by
    have h2 := addOrderOf_nsmul_eq_zero (hP D p)
    rwa [h1, one_nsmul] at h2)
  obtain ⟨k, hk⟩ := hodd
  omega

def partner (D : D7) (p : ℕ) (t : HH D) (e : ℕ) : Bool × HH D :=
  (decide (IsSg D p ∧ Odd e), t + e • hP D p)

def IsTopPl (D : D7) (z : Bool × HH D) : Prop := z.1 = false ∧ z.2 ∈ D.host.TT

def IsThickPl (D : D7) (z : Bool × HH D) : Prop :=
  z.1 = true ∧ z.2 ∈ D.host.T2.image (fun s : ℕ => D.R.dig s + D.host.u0)

def IsThinPl (D : D7) (z : Bool × HH D) : Prop := ¬ IsTopPl D z ∧ ¬ IsThickPl D z

structure Inst (D : D7) (L : SizeData₂ D) where
  bs : HH D → HH D → HH D
  bs_orb : ∀ h t, ∃ i : ℕ, bs h t + i • h = t
  bs_step : ∀ h t, bs h (t + h) = bs h t
  off : ℕ → Bool × HH D → ℝ
  off_top : ∀ j z, IsTopPl D z → L.sc.b' / L.sc.x ≤ off j z ∧ off j z ≤ L.sc.b' / L.sc.x + L.etaSz
  off_thin : ∀ j z, IsThinPl D z → L.sc.w'' D.R.n ≤ off j z ∧ off j z ≤ L.sc.w'' D.R.n + L.etaSz
  off_thick : ∀ j z, IsThickPl D z → L.sc.b ≤ off j z ∧ off j z ≤ L.sc.b + L.etaSz + 1
  kapI : ℕ → (n' : ℕ) → Finset (Fin n') → (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ
  ep : ℕ → ℕ

variable {D : D7} {L : SizeData₂ D}

def fill (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ :=
  (if z.1 = false ∧ z.2 ∈ D.host.TT then (b z.2 : ℝ) else 0) + X.off j z

def kaJ (D : D7) (j : ℕ) : ℝ := ((D.R.k : ℝ) + (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)) / 2

def fillG (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (z : Bool × HH D) : ℝ := fill X b j z - kaJ D j

def stepP (D : D7) (p : ℕ) : HH D := if IsSg D p then 2 • hP D p else hP D p

def nP (D : D7) (p : ℕ) : ℕ :=
  if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p)

def reps (X : Inst D L) (p : ℕ) : Finset (HH D) := Finset.univ.image (X.bs (stepP D p))

def topsOn (X : Inst D L) (p : ℕ) (t0 : HH D) : Finset (HH D) :=
  D.host.TT.filter (fun t => X.bs (stepP D p) t = t0)

def Nv (X : Inst D L) (p : ℕ) (t0 : HH D) : ℕ := (topsOn X p t0).card

def topsPos (D : D7) (p : ℕ) (t0 : HH D) : Finset (Fin (addOrderOf (hP D p))) :=
  Finset.univ.filter (fun i => t0 + (i : ℕ) • hP D p ∈ D.host.TT)

def wPos (D : D7) (p : ℕ) (t0 : HH D) (a : HH D → ℤ) : Fin (addOrderOf (hP D p)) → ℤ :=
  fun i => a (t0 + (i : ℕ) • hP D p)

def IsV (X : Inst D L) (p : ℕ) (t : HH D) : Prop :=
  ∃ i : ℕ, i < nP D p ∧ Even i ∧ X.bs (stepP D p) t + i • hP D p = t

def Good (_X : Inst D L) (p : ℕ) (t0 : HH D) : Prop :=
  IsGoodOrbit (addOrderOf (hP D p)) (topsPos D p t0) (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1
    (hG L.sc) L.sc.x

def NplusF (s : Scale) (n' : ℕ) : ℝ := 40 * (n' : ℝ) * s.delta1

def DIIf (K : Consts) (L : SizeData₂ D) (p n' : ℕ) : ℕ :=
  ⌈K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) *
      Real.logb p L.sc.a + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L +
      (rG L.sc : ℝ) * NplusF L.sc n' * c0num L⌉₊

def DIf (K : Consts) (L : SizeData₂ D) (p n' : ℕ) : ℕ :=
  ⌈K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
      Real.logb p L.sc.a⌉₊

def tIIf (K : Consts) (L : SizeData₂ D) (p n' N : ℕ) : ℝ :=
  K.tII * (rG L.sc : ℝ) * (N : ℝ) * (La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
    L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) + c0num L + (D.R.k : ℝ) * Qp L.sc p) +
    2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L

def kapIIf (K : Consts) (L : SizeData₂ D) (N : ℕ) : ℝ :=
  min 1 (K.kII * (N : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) * L.sc.x ^ (-Scale.A))

open Classical in

def dMinus {n' : ℕ} (TT : Finset (Fin n')) (y : Fin n') : ℕ :=
  if h : ∃ d : ℕ, 0 < d ∧ d ≤ n' ∧ posAdd y (n' - d) ∈ TT ∧ IsTypeV (posAdd y (n' - d))
  then Nat.find h else 0

def c6f (K : Consts) (L : SizeData₂ D) (p n' : ℕ) : ℝ :=
  8 * ((DIf K L p n' : ℝ) + 1) + K.kappaThresholdTwo * NplusF L.sc n' * (D.R.k : ℝ) * Real.logb p L.sc.a +
    4 * NplusF L.sc n' * cG L + 2 * (n' : ℝ) * cG L

open Classical in

def tIf (K : Consts) (L : SizeData₂ D) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) : ℝ :=
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

def al (L : SizeData₂ D) (a : HH D → ℤ) (s : HH D) : ℝ := (a s : ℝ) - 2 * cG L

def capU (X : Inst D L) (b : HH D → ℤ) (p j : ℕ) (s : HH D) (e : ℕ) : ℝ :=
  fillG X b j (partner D p s e) + cG L

def IsDist (D : D7) (p : ℕ) (s s' : HH D) (e : ℕ) : Prop :=
  0 < e ∧ partner D p s e = (false, s') ∧ ∀ e', 0 < e' → e' < e → partner D p s e' ≠ (false, s')

def Excl (D : D7) (p : ℕ) (s : HH D) (e : ℕ) : Prop :=
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

def Dp (K : Consts) (L : SizeData₂ D) (p : ℕ) : ℕ :=
  if (p : ℝ) < L.sc.p0 D.R.k then DIIf K L p (nP D p) else DIf K L p (nP D p)

def tv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  if (p : ℝ) < L.sc.p0 D.R.k then tIIf K L p (nP D p) (Nv X p t0)
  else tIf K L p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def kapv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) (wPos D p t0 a) (wPos D p t0 b)

def Cand (D : D7) (L : SizeData₂ D) (K : Consts) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℝ) < L.sc.X' ∧ IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) ∧
    (L.sc.p0 D.R.k ≤ (p : ℝ) → ¬ InBand D K L.sc p)

open Classical in

def goodReps (X : Inst D L) (p : ℕ) : Finset (HH D) := (reps X p).filter (fun t0 => Good X p t0)

def Sig (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : ℝ :=
  (D.R.m : ℝ) * ∑ t0 ∈ goodReps X p, kapv X K a b p t0

open Classical in

def VV (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) : Finset (HH D) :=
  if Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) then goodReps X p else ∅

def ServedOrbitsContained (X : Inst D L) (K : Consts) (a b : HH D → ℤ) : Prop :=
  ∀ p, Cand D L K p → Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) → goodReps X p ⊆ VV X K a b p

theorem served_orbits_in_set (X : Inst D L) (K : Consts) (a b : HH D → ℤ) : ServedOrbitsContained X K a b := by
  intro p hc hs
  have hv : VV X K a b p = goodReps X p := by
    unfold VV
    exact if_pos ⟨hc, hs⟩
  exact hv ▸ Finset.Subset.refl (goodReps X p)

def winA (D : D7) (s : Scale) : Finset ℤ :=
  Finset.Icc ⌈s.a⌉ ⌊s.a + s.a / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))⌋

def winB (D : D7) (K : Consts) (s : Scale) : Finset ℤ :=
  Finset.Icc ⌈s.b'⌉ ⌊s.b' + Nstar D s * s.x ^ s.eps * La K s * s.b' / D.R.k⌋

open Classical in

def box (D : D7) (W : Finset ℤ) : Finset (HH D → ℤ) :=
  Fintype.piFinset (fun t => if t ∈ D.host.TT then W else {0})

def meanW (D : D7) (K : Consts) (s : Scale) (F : (HH D → ℤ) → (HH D → ℤ) → ℝ) : ℝ :=
  (∑ a ∈ box D (winA D s), ∑ b ∈ box D (winB D K s), F a b) /
    (((box D (winA D s)).card : ℝ) * ((box D (winB D K s)).card : ℝ))

open Classical in

def boxLoc (n' : ℕ) (TT : Finset (Fin n')) (W : Finset ℤ) : Finset (Fin n' → ℤ) :=
  Fintype.piFinset (fun i => if i ∈ TT then W else {0})

def meanLoc (D : D7) (K : Consts) (s : Scale) (n' : ℕ) (TT : Finset (Fin n'))
    (F : (Fin n' → ℤ) → (Fin n' → ℤ) → ℝ) : ℝ :=
  (∑ a ∈ boxLoc n' TT (winA D s), ∑ b ∈ boxLoc n' TT (winB D K s), F a b) /
    (((boxLoc n' TT (winA D s)).card : ℝ) * ((boxLoc n' TT (winB D K s)).card : ℝ))

def MeanKappaBound (X : Inst D L) (K : Consts) : Prop :=
  ∀ p, Cand D L K p → ∀ t0 ∈ goodReps X p,
    meanLoc D K L.sc (addOrderOf (hP D p)) (topsPos D p t0)
      (fun a b => kapLoc X K p (addOrderOf (hP D p)) (topsPos D p t0) a b) ≤ (Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ) ∧
    ((p : ℝ) < L.sc.p0 D.R.k → ∀ a b, kapv X K a b p t0 ≤ (Nv X p t0 : ℝ) * L.sc.x ^ (-12 : ℝ))

def Sv (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (t0 : HH D) : ℝ :=
  (⌈∑ j ∈ SizeData₂.lifts D, max 0 (gU X K a b p j t0 - Pr X K b p j t0 - max (g0 X K a b p j t0) 0)⌉ : ℤ)

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

open Classical in

def askG (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e : ℕ, if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - fillG X b j (partner D p s e)) else 0

open Classical in

def askP (X : Inst D L) (a b : HH D → ℤ) (p j : ℕ) (s : HH D) : ℝ :=
  ∑' e : ℕ, if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e - fill X b j (partner D p s e)) else 0

open Classical in

def lo (K : Consts) (L : SizeData₂ D) (C bo : ℝ) (p : ℕ) : ℝ :=
  let s := L.sc
  let cp : ℝ := C * (cG L + L.etaSz) * Real.logb p (2 * s.a)
  let pr : ℝ := if IsResidueClassZero D p then
      (if (p : ℝ) < s.p0 D.R.k then C * (rG s : ℝ) * s.b' * Real.log s.x
       else if (p : ℝ) < s.X' then
         s.b' / s.x + L.etaSz + C * s.w'' D.R.n * Real.log s.x / s.delta1 + bo
       else 0) else 0
  let orr : ℝ := if IsResidueClassZero D p ∧ (p : ℝ) < s.X' then
      C * Real.log s.x * (La K s * s.a / ((p : ℝ) * D.R.k) +
        (if (p : ℝ) < s.p0 D.R.k then s.a * (p : ℝ) ^ (-(L1 D s p : ℝ)) else s.a / (p : ℝ) ^ 2))
      else 0
  cp + pr + orr

def fl (D : D7) (s : Scale) (C : ℝ) (p : ℕ) : ℝ :=
  C * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p s.a + C * (D.R.f : ℝ) * Real.logb p s.a ^ 2

def aL (L : SizeData₂ D) (t : HH D) : ℤ := if h : t ∈ D.host.TT then L.aT ⟨t, h⟩ else 0

def bL (L : SizeData₂ D) (t : HH D) : ℤ := if h : t ∈ D.host.TT then L.bT ⟨t, h⟩ else 0

def plGG (D : D7) (z : Bool × HH D) : D.R.GG := if z.1 then D.R.tau2 z.2 else D.R.tau1 z.2

def ParametersFill (X : Inst D L) (K : Consts) (w : D.what₂.places.Pl) : Prop :=
  let p := D.what₂.places.resChar w
  (∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D), (D.eTau τ : D.R.GG) = plGG D z →
    fill X (bL L) j z = wj D j τ) ∧
  (∀ j (t : D.host.TT) e, L.wPart j t p e = fill X (bL L) j (partner D p t e)) ∧
  (L.TTw w).map (Function.Embedding.subtype _) = TTP X K (aL L) (bL L) p ∧
  (w ∈ L.supp → (IsResidueClassZero D p ∨ IsSg D p) →
    ∀ j ∈ SizeData₂.lifts D, L.gain j w = gainP X K (aL L) (bL L) p j) ∧
  L.tau w = tauP X K (aL L) (bL L) p ∧ L.io w = ioP X K (aL L) (bL L) p ∧
  La K L.sc = L.LaG

def vUnit {p : ℕ} (G : GAtP p) : ℝ := ((IsDiscreteValuationRing.addVal G.O (p : G.O)).toNat : ℝ)

def vGeLat {p : ℕ} (G : GAtP p) {V : Type} [AddCommGroup V] [Module G.Kf V] [Module G.O V]
    [IsScalarTower G.O G.Kf V] (N : Submodule G.O V) (F : V) (g : ℝ) : Prop :=
  ∃ ϖ : G.O, Irreducible ϖ ∧ F ∈ scale ((algebraMap G.O G.Kf ϖ) ^ ⌈g * vUnit G⌉) N

structure LatInst (D : D7) where
  vOf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), HH D → Fin (D.gat u w hg).P.nV
  Fl : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Fills (D.gat u w hg)
  Lv : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Levels (Fl u w hg)
  Ch : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Chain (Lv u w hg)
  Vram : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn

def LatInst.vKge (Y : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (F : (D.gat u w hg).Fn) (g : ℝ) : Prop :=
  vGeLat (D.gat u w hg) ((Y.Lv u w hg).Int D.R.m) ((Y.Ch u w hg).chainK D.R.m F) g

def LatTied (hT : GatTies D) (X : Inst D L) (Y : LatInst D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    let p := D.what₂.places.resChar w
    (Y.Fl u w hg).mm = D.R.m ∧ (Y.Fl u w hg).t = D.R.t ∧
    ((Y.Fl u w hg).c : ℝ) ≤ cG L ∧
    (D.gat u w hg).P.r = (if (p : ℝ) < L.sc.p0 D.R.k then rG L.sc else 1) ∧
    Set.InjOn (Y.vOf u w hg) (reps X p) ∧
    (∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (t : HH D),
      ((D.eTau (hT.gat_pos u w hg ⟨v, s⟩) : D.R.Psi) : D.R.GG) = D.R.tau2 t →
        s ∉ (Y.Fl u w hg).TT v ∧
        ∀ j ∈ SizeData₂.lifts D, ((Y.Fl u w hg).w v j s : ℝ) = fillG X (bL L) j (true, t)) ∧
    ∀ t0 ∈ reps X p,
      (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (hP D p) ∧
      ∀ s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)),
        ((D.eTau (hT.gat_pos u w hg ⟨Y.vOf u w hg t0, s⟩) : D.R.Psi) : D.R.GG) =
          D.R.tau1 (t0 + s.val • hP D p) ∧
        (s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) ↔ t0 + s.val • hP D p ∈ D.host.TT) ∧
        (s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
          (Y.Fl u w hg).a (Y.vOf u w hg t0) s = aL L (t0 + s.val • hP D p) ∧
          (Y.Fl u w hg).b (Y.vOf u w hg t0) s = bL L (t0 + s.val • hP D p)) ∧
        ∀ j ∈ SizeData₂.lifts D,
          ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) = fillG X (bL L) j (false, t0 + s.val • hP D p)

def yProd (Y : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (VV' : Finset (HH D)) (F : (D.gat u w hg).Fn) : (D.gat u w hg).Fn :=
  (VV'.toList.map (fun t0 => ((D.gat u w hg).yv (Y.vOf u w hg t0))^[D.R.m])).foldr
    (fun f g => f ∘ g) id F

def lowFE (L : SizeData₂ D) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  ∑ j ∈ SizeData₂.lifts D, ((L.F j w : ℝ) - (L.E u j w : ℝ))

open Classical in

def NP (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn :=
  let p := D.what₂.places.resChar w
  let G := D.gat u w hg
  let VVp := VV X K (aL L) (bL L) p
  Submodule.span G.O {F' | ∃ VV' ⊆ VVp, ∃ F ∈ G.M,
      F' = yProd Y u w hg VV' (((p : G.O) ^ (∑ t0 ∈ VVp \ VV', ⌈Sv X K (aL L) (bL L) p t0⌉.toNat)) • F)} ⊓
    G.M.map (((p : G.O) ^ ⌈tauP X K (aL L) (bL L) p⌉.toNat) • LinearMap.id) ⊓ Y.Vram u w hg

def LatticeLengthsAtPlace (X : Inst D L) (Y : LatInst D) (K : Consts) (w : D.what₂.places.Pl) : Prop :=
  (w ∈ L.supp → ∀ (u : D.what₂.Word) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ l : ℕ, Module.length (D.gat u w hg).O
        (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
          (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) = l ∧
      (l : ℝ) = (L.lenMN u w : ℝ) * vUnit (D.gat u w hg)) ∧
  ∀ u : D.what₂.Word, VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ →
    D.what₂.places.resChar w ≠ (D.mem u).A.T → L.lenMN u w = 0

end Formalism.MainNotions.G

end
