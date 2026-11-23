import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LogFactorialIndices.StatementSize
import Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
import Formalism.MirabolicMackeyTheory.StatementT

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped BigOperators

abbrev RPl (R : Ranks) : Type := Bool × R.A

structure NumDatum where

  R : Ranks

  sc : Scale

  H : Formalism.HC.HostAx R.toFrame

  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime

  TT : Finset (R.A)

  Del : ℕ

  h0 : ℕ

  hc : RPl R → HCParam R

abbrev Code (N : NumDatum) : Type := Fin (N.R.k - 2) → Bool

namespace NumDatum

variable (N : NumDatum)

abbrev q : ℕ := N.H.q

abbrev d : ℕ := N.H.d

theorem hyp : HostHyp N.q N.d := N.H.hyp

def Nm : ℕ := N.R.N N.R.m

def lifts : Finset ℕ := Finset.Icc 1 N.R.m

def Sc : ℝ := (N.R.k : ℝ) * (4 * (N.Del : ℝ))

def eta : ℝ := (N.R.m : ℝ) * (N.h0 : ℝ)

def rd : ℝ := N.H.rd

def v : ℝ := N.rd / 2

def cond : ℕ := N.H.condN

def chiK : DirichletCharacter ℂ N.d :=
  haveI : Fact N.d.Prime := ⟨N.hyp.2.1⟩
  (quadraticChar (ZMod N.d)).ringHomComp (Int.castRingHom ℂ)

def logDerivativeAtOne : ℝ :=
  haveI : NeZero N.d := ⟨N.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction N.chiK) 1 / DirichletCharacter.LFunction N.chiK 1).re

def logOm : ℝ := Real.eulerMascheroniConstant + Real.log (Real.pi / N.v) - N.logDerivativeAtOne

def La : ℝ := Real.log (N.sc.a * N.rd)

def Lp : ℝ := Real.log (N.sc.b * N.rd * ((N.g 0 : ℝ) * (N.g 1 : ℝ)) * (N.R.nV : ℝ))

def B0 : ℝ := (N.R.f : ℝ) * N.R.m * N.sc.b * N.sc.x ^ N.sc.eps

end NumDatum

def hFrob (e p : ℕ) : ZMod (2 ^ e) :=
  if h : Nat.Coprime p (2 ^ (e + 2)) then iotaHInv e (hcl e (ZMod.unitOfCoprime p h)) else 0

def frobUnitMod (M p : ℕ) : (ZMod M)ˣ := by
  classical
  exact if h : ∃ w : (ZMod M)ˣ, ((w : ZMod M).cast : ZMod (ordCompl[p] M)) = (p : ZMod (ordCompl[p] M)) ∧
    ((w : ZMod M).cast : ZMod (ordProj[p] M)) = 1 then h.choose else 1

def hArt {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) : φ.A :=
  φ.iotaInv (H.art (frobUnitMod H.condN p)).2

theorem frobUnitMod_of_coprime {M p : ℕ} (h : Nat.Coprime p M) : frobUnitMod M p = ZMod.unitOfCoprime p h := by
  have h0 : M.factorization p = 0 := by
    by_cases hp : p.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 h)
    · exact Nat.factorization_eq_zero_of_not_prime M hp
  have k1 : ∀ (A : ℕ), A = M → ∀ w : ZMod M, ((w.cast : ZMod A) = (p : ZMod A) ↔ w = (p : ZMod M)) := by
    rintro A rfl w
    rw [ZMod.cast_id]
  have k2 : ∀ (B : ℕ), B = 1 → ∀ w : ZMod M, (w.cast : ZMod B) = 1 := by
    rintro B rfl w
    exact Subsingleton.elim _ _
  have key : ∀ w : (ZMod M)ˣ, (((w : ZMod M).cast : ZMod (ordCompl[p] M)) = (p : ZMod (ordCompl[p] M)) ∧
      ((w : ZMod M).cast : ZMod (ordProj[p] M)) = 1) ↔ w = ZMod.unitOfCoprime p h := by
    intro w
    rw [k1 _ (by rw [h0, pow_zero, Nat.div_one]), and_iff_left (k2 _ (by rw [h0, pow_zero]) _), Units.ext_iff,
      ZMod.coe_unitOfCoprime]
  have hex : ∃ w : (ZMod M)ˣ, ((w : ZMod M).cast : ZMod (ordCompl[p] M)) = (p : ZMod (ordCompl[p] M)) ∧
      ((w : ZMod M).cast : ZMod (ordProj[p] M)) = 1 := ⟨_, (key _).2 rfl⟩
  unfold frobUnitMod
  rw [dif_pos hex]
  exact (key _).1 hex.choose_spec

namespace NumDatum

variable (N : NumDatum)

def cls (p : ℕ) : PrimeClass := primeClass N.H.toHostRaw p

def hP (p : ℕ) : N.R.A :=
  if h : Nat.Coprime p N.H.condN then N.R.iotaInv (N.H.art (ZMod.unitOfCoprime p h)).2
  else N.R.iotaInv (N.H.art (frobUnitMod N.H.condN p)).2

theorem hP_eq_hArt (p : ℕ) : N.hP p = hArt N.H.toHostRaw p := by
  unfold hP hArt
  split
  · rename_i h
    rw [frobUnitMod_of_coprime h]
  · rfl

def pos (p : ℕ) (z : RPl N.R) (s : ℕ) : RPl N.R :=
  (xor z.1 (decide (N.cls p = PrimeClass.signal ∧ Odd s)), z.2 + s • N.hP p)

def ordP (p : ℕ) : ℕ :=
  if N.cls p = PrimeClass.signal then 2 * addOrderOf (2 • N.hP p) else addOrderOf (N.hP p)

instance ordP_neZero (p : ℕ) : NeZero (N.ordP p) := by
  refine ⟨?_⟩
  unfold ordP
  split
  · exact (Nat.mul_pos two_pos (addOrderOf_pos _)).ne'
  · exact (addOrderOf_pos _).ne'

def swapP (p : ℕ) : Prop :=
  N.cls p = PrimeClass.signal ∨ (N.cls p = PrimeClass.splitK ∧ N.H.psAt p = -1)

instance swapP_decidable (p : ℕ) : Decidable (N.swapP p) :=
  inferInstanceAs (Decidable (_ ∨ _))

def posS (p : ℕ) (z : RPl N.R) (s : ℕ) : RPl N.R :=
  (xor z.1 (decide (N.swapP p ∧ Odd s)), z.2 + s • N.hP p)

def ordPS (p : ℕ) : ℕ :=
  if N.swapP p then 2 * addOrderOf (2 • N.hP p) else addOrderOf (N.hP p)

instance ordPS_neZero (p : ℕ) : NeZero (N.ordPS p) := by
  refine ⟨?_⟩
  unfold ordPS
  split
  · exact (Nat.mul_pos two_pos (addOrderOf_pos _)).ne'
  · exact (addOrderOf_pos _).ne'

def eQ (j : ℕ) (z : RPl N.R) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ N.R.m then (N.hc z).e ⟨j - 1, by omega⟩ else 0

def w (j : ℕ) (z : RPl N.R) : ℝ := ((N.eQ j z : ℚ) : ℝ)

def FOrb (j p : ℕ) (z : RPl N.R) : ℝ :=
  lpF p (N.ordP p) (fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos p z s.val))

open Classical in

def FInert (j p : ℕ) : ℝ :=
  if N.cls p = PrimeClass.inertClass ∧ N.hP p = 0 then
    ∑ z : RPl N.R, ((N.R.k : ℝ) - 1) * N.w j z / ((p : ℝ) ^ 2 - 1)
  else (∑ z : RPl N.R, N.FOrb j p z) / (N.ordP p : ℝ)

def FRamD (j : ℕ) : ℝ :=
  -(((N.R.k : ℝ) - 1) / 2) * ∑ t : N.R.A, min (N.w j (false, t)) (N.w j (true, t))

def sigPar (z : RPl N.R) (i : ℕ) : ℚ :=
  if h : i < N.R.k - 1 then (N.hc z).v ⟨i, h⟩
  else if hb : i - (N.R.k - 1) < N.R.m then -(N.hc z).b ⟨i - (N.R.k - 1), hb⟩ else 0

def aPlus (j : ℕ) (z : RPl N.R) (i : ℕ) : ℚ :=
  N.sigPar z i + N.eQ j z - ((N.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((N.R.k : ℚ) + j - 1) - ((N.R.m : ℚ) - j)) / 2

def aMinus (j : ℕ) (z : RPl N.R) (c : ℕ) : ℚ :=
  (if h : j + c < N.R.m then (N.hc z).b ⟨j + c, h⟩ else 0) - N.eQ j z - ((N.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

def Dplus (j : ℕ) : ℚ := ∑ z : RPl N.R, ∑ i ∈ Finset.range (N.R.sigW j).1, N.aPlus j z i

def Dminus (j : ℕ) : ℚ := ∑ z : RPl N.R, ∑ c ∈ Finset.range (N.R.sigW j).2, N.aMinus j z c

def FTypeG (j : ℕ) : ℝ := -(((N.Dplus j + N.Dminus j : ℚ) : ℝ)) / 2

open Classical in

def FjP (j p : ℕ) : ℝ :=
  if p = N.g 0 ∨ p = N.g 1 then N.FTypeG j
  else if N.cls p = PrimeClass.ramD then N.FRamD j
  else if (N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal) ∧ (p : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j p
  else 0

def Fj {K : Type} [Field K] [NumberField K] (j : ℕ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  N.FjP j (Formalism.EigenvalueLevelCeiling.plc w)

def suppP : Finset ℕ :=
  ((Finset.range (⌊N.sc.X'' N.R.n⌋₊ + 1)).filter Nat.Prime) ∪ {N.g 0, N.g 1, N.d}

def Fo : ℝ := ∑ j ∈ N.lifts, ∑ p ∈ N.suppP, Real.log p * N.FjP j p

def uW (δ : Code N) (z : RPl N.R) (i : Fin N.R.k) : ℚ :=
  if h : 1 ≤ i.1 ∧ i.1 + 1 < N.R.k then
    (N.hc z).v ⟨i.1 - 1, by omega⟩ - 1 / 2 - (if δ ⟨i.1 - 1, by omega⟩ then (N.Del : ℚ) else 0)
  else (N.hc z).u i

def srcPar (δ : Code N) (z : RPl N.R) (i : ℕ) : ℚ :=
  if h : i < N.R.k then N.uW δ z ⟨i, h⟩
  else
    if hb : (i - N.R.k) / (N.R.t + 1) < N.R.m then
      -(N.hc z).e ⟨(i - N.R.k) / (N.R.t + 1), hb⟩ +
        ((N.R.t : ℚ) + 2 - 2 * (((i - N.R.k) % (N.R.t + 1) + 1 : ℕ) : ℚ)) / 2
    else 0

def nu (δ : Code N) (j : ℕ) (z : RPl N.R) (i : ℕ) : ℚ :=
  N.srcPar δ z i + N.eQ j z - (((N.R.N (j - 1) : ℚ) + N.R.N j - 1 - 2 * (i : ℚ)) / 2)

def nuAbs (δ : Code N) (j : ℕ) (z : RPl N.R) : ℚ := ∑ i ∈ Finset.range (N.R.N (j - 1)), N.nu δ j z i

def Dpi (δ : Code N) (j : ℕ) : ℚ := ∑ z : RPl N.R, N.nuAbs δ j z

def wN (j : ℕ) (z : RPl N.R) : ℕ := ⌊N.eQ j z⌋.toNat

def nuN (δ : Code N) (j : ℕ) (z : RPl N.R) (i : ℕ) : ℕ := ⌊N.nu δ j z i⌋.toNat

def apN (j : ℕ) (z : RPl N.R) (i : ℕ) : ℕ := ⌊N.aPlus j z i⌋.toNat

def nuRows (δ : Code N) (j : ℕ) (z : RPl N.R) : Multiset ℕ := (Multiset.range (N.R.N (j - 1))).map (N.nuN δ j z)

def apRows (j : ℕ) (z : RPl N.R) : Multiset ℕ := (Multiset.range (N.R.sigW j).1).map (N.apN j z)

def apDiag (j : ℕ) (z : RPl N.R) : YoungDiagram :=
  YoungDiagram.ofRowLens (((List.range (N.R.sigW j).1).map (N.apN j z)).insertionSort (· ≥ ·))
    List.sortedGE_insertionSort

def logHook (j : ℕ) (z : RPl N.R) : ℝ := Real.log (Formalism.LatticeIndexTer.hookProd (N.apDiag j z) : ℝ)

def aT (t : N.R.A) : ℚ :=
  (N.hc (false, t)).u ⟨0, by have := N.R.m_add_three_le_k; omega⟩ - ((N.R.k : ℚ) - 1) / 2

def bT (t : N.R.A) : ℚ :=
  -(N.hc (false, t)).u ⟨N.R.k - 1, by have := N.R.m_add_three_le_k; omega⟩ - ((N.R.k : ℚ) - 1) / 2

def hA (C : ℝ) (T : ℕ) : ℝ :=
  -(∑ t ∈ N.TT, ((N.aT t : ℚ) : ℝ) * Real.log (T : ℝ)) +
    C * ((N.TT.card : ℝ) * N.sc.b' * (N.Nm : ℝ) +
      (N.R.f : ℝ) * ((N.R.m : ℝ) * N.eta + N.Sc) * (N.Nm : ℝ) + (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2) * N.La

def kerPlace (δ : Code N) (j : ℕ) (z : RPl N.R) : ℝ :=
  (∑ i ∈ Finset.range (N.R.N (j - 1)), Formalism.LatticeIndexTer.ph ((N.nu δ j z i : ℚ) : ℝ)) - ((N.nuAbs δ j z : ℚ) : ℝ) * N.logOm

def hB (C : ℝ) (δ : Code N) (j : ℕ) : ℝ :=
  (∑ z : RPl N.R, N.kerPlace δ j z) + C * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * N.La +
    C * (N.R.f : ℝ) * (N.R.m : ℝ) ^ 3 * (N.Nm : ℝ) ^ 2 * N.sc.L

def hX (C : ℝ) (j : ℕ) : ℝ :=
  (∑ z : RPl N.R, N.logHook j z) - C * (N.R.f : ℝ) * (N.R.nV : ℝ) ^ 2 * N.Lp

def hU (C : ℝ) (δ : Code N) (T : ℕ) : ℝ :=
  N.hA C T + (∑ j ∈ N.lifts, N.hB C δ j) - ∑ j ∈ N.lifts, N.hX C j

def mainT (T : ℕ) : ℝ :=
  ∑ t ∈ N.TT, ((N.R.m : ℝ) * (Formalism.LatticeIndexTer.ph ((N.aT t : ℚ) : ℝ) - ((N.aT t : ℚ) : ℝ) * N.logOm) -
    ((N.aT t : ℚ) : ℝ) * Real.log (T : ℝ))

def ctD (δ : Code N) (j : ℕ) (t : N.R.A) : ℚ :=
  N.nuAbs δ j (false, t) - (if t ∈ N.TT then N.nu δ j (false, t) 0 - N.nu δ j (false, t) 1 else 0) +
    (if t ∈ N.TT then N.nu δ j (true, t) 0 else 0)

def EatD (W : Finset (Code N)) (hW : W.Nonempty) (j : ℕ) : ℝ :=
  N.FRamD j + (W.sup' hW fun δ => ((∑ t : N.R.A, N.ctD δ j t : ℚ) : ℝ)) / 2

def exch : ℝ := (N.R.f : ℝ) * N.R.k * (N.Nm : ℝ)

def EatC (cdig : ℝ) (j p : ℕ) : ℝ :=
  cdig * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * Real.logb p N.sc.a + (∑ z : RPl N.R, N.w j z) / ((p : ℝ) ^ 2 - 1)

def EatG (C : ℝ) (δ : Code N) (j : ℕ) (bar : Bool) : ℝ :=
  N.FTypeG j + (if bar then ((N.Dpi δ j : ℚ) : ℝ) else 0) +
    C * (N.R.f : ℝ) * ((N.Nm : ℝ) ^ 2 + (N.R.m : ℝ) ^ 2 * N.eta)

open Classical in

def kindA (p : ℕ) : Finset (RPl N.R) := Finset.univ.filter fun z => ¬ N.cls p = PrimeClass.signal ∧ z.1 = false

open Classical in

def kindBC (p : ℕ) : Finset (RPl N.R) := Finset.univ.filter fun z => N.cls p = PrimeClass.signal ∨ z.1 = true

open Classical in

def topsBC (p : ℕ) : Finset (RPl N.R) := (N.kindBC p).filter fun z => z.1 = false ∧ z.2 ∈ N.TT

def IsCs (p : ℕ) : Prop := N.cls p = PrimeClass.inertClass ∧ Odd (addOrderOf (N.hP p)) ∧ N.hP p ≠ 0

open Classical in

def EatX (c6 : ℝ) (j p : ℕ) : ℝ :=
  if N.IsCs p then
    ((N.R.k : ℝ) - 1) * (∑ z ∈ N.kindBC p, N.w j z) / (p : ℝ) ^ 3 +
      c6 * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * Real.logb p N.sc.a
  else 0

def EatI (c6 dl1 dl2 : ℝ) (j p : ℕ) : ℝ :=
  max 0 ((∑ z ∈ N.kindA p, N.FOrb j p z) / (N.ordP p : ℝ)) +
    (p : ℝ) / ((p : ℝ) ^ 2 - 1) * ((N.topsBC p).card : ℝ) * (N.sc.b + N.eta + 1 + 3 * N.Sc) +
    c6 * (∑ z ∈ N.kindBC p, N.w j z) / (p : ℝ) +
    ((N.kindBC p).card : ℝ) * (N.R.N (j - 1) : ℝ) * (N.R.N j : ℝ) *
      (Real.logb p (4 * (N.ordP p : ℝ) * (N.Nm : ℝ) * N.sc.a) + 1) +
    (dl1 * ((N.kindBC p).card : ℝ) * (N.Nm : ℝ) ^ 2 * Real.logb p (2 * N.sc.a) +
      dl2 * ((N.topsBC p).card : ℝ) * Real.logb p (2 * N.sc.a) ^ 2) +
    N.EatX c6 j p

end NumDatum

end Formalism.L2.DIV

end
