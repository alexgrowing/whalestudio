import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain

structure Scale where
  x : ℝ
  eps : ℝ
  one_lt_alt : 1 < x
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52

  J : ℝ
  one_le_J : 1 ≤ J

namespace Scale

variable (s : Scale)

def ez : ℝ := s.eps / s.J
theorem ez_pos : 0 < s.ez := div_pos s.eps_pos (lt_of_lt_of_le one_pos s.one_le_J)
theorem ez_le : s.ez ≤ s.eps := div_le_self s.eps_pos.le s.one_le_J

def L : ℝ := s.x ^ s.eps

def b : ℝ := Real.exp s.L

def a : ℝ := s.x * s.b

def X' : ℝ := Real.exp (s.x ^ (s.eps / 3))

def b' : ℝ := s.a / s.X'

def w'' (n : ℕ) : ℝ := s.b' / (s.x * n)

def X'' (n : ℕ) : ℝ := s.a / s.w'' n

def A : ℝ := 26

def p0 (k : ℕ) : ℝ := (k : ℝ) ^ 2 * s.x ^ A

def delta1 : ℝ := s.x ^ (-(s.eps / 8))

end Scale

def phF (y : ℝ) : ℝ := y * Real.log y - y

def lpFeasible (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : Set ℝ :=
  {y | ∃ xs : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, (¬ Odd i ∨ d ≤ i) → xs s i = 0) ∧
    (∀ s, (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ Ds s) ∧
    y = ∑ s, ∑ i ∈ Finset.range d, xs s i}

def lpF (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : ℝ :=
  (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - sSup (lpFeasible l d Ds)

def Gfun (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (y / n - 1)) -
    y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

def chiK (D : D7) : DirichletCharacter ℂ D.host.d :=
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  (quadraticChar (ZMod D.host.d)).ringHomComp (Int.castRingHom ℂ)

def dlogL (D : D7) (s : ℂ) : ℝ :=
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction (chiK D)) s / DirichletCharacter.LFunction (chiK D) s).re

def wj (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if h : j - 1 < D.R.m then (((D.hc τ).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

structure SizeData₂ (D : D7) where
  sc : Scale

  aT : D.host.TT → ℤ
  aT_win : ∀ t, sc.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ sc.a + sc.a / ((D.R.k : ℝ) * sc.x ^ (Scale.A / 2))

  bT : D.host.TT → ℤ
  bT_ge : ∀ t, sc.b' ≤ (bT t : ℝ)

  top_u : ∀ τ (t : D.host.TT) (h0 : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).u ⟨0, h0⟩ : ℚ) : ℝ) = aT t + ((D.R.k : ℝ) - 1) / 2 ∧
    (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) = -(bT t : ℝ) - ((D.R.k : ℝ) - 1) / 2
  top_b : ∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3

  supp : Finset D.what₂.places.Pl

  gain : ℕ → D.what₂.places.Pl → ℝ
  F : ℕ → D.what₂.places.Pl → ℝ
  E : D.what₂.Word → ℕ → D.what₂.places.Pl → ℝ
  tau : D.what₂.places.Pl → ℝ
  io : D.what₂.places.Pl → ℝ
  gain_supp : ∀ j w, w ∉ supp → gain j w = 0
  F_supp : ∀ j w, w ∉ supp → F j w = 0
  E_supp : ∀ u j w, w ∉ supp → E u j w = 0
  tau_supp : ∀ w, w ∉ supp → tau w = 0
  io_supp : ∀ w, w ∉ supp → io w = 0

  gain_g : ∀ j w, D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) → gain j w = 0

  b_le : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2

  untwisted : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0 ∧ F j w = 0

  not_inert : ∀ w, D.host.cls (D.what₂.places.resChar w) ≠ .signal →
    D.host.cls (D.what₂.places.resChar w) ≠ .inertClass → (∀ j, gain j w = 0) ∧ tau w = 0 ∧ io w = 0

  drop : Set ℕ
  drop_alt : ∀ u, (D.mem u).A.T ∉ drop

  F_conj : ∀ j w, F j (D.what₂.places.conj w) = F j w

  F_above : ∀ j w, sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ) →
    D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    D.what₂.places.resChar w ≠ D.host.d → F j w = 0

  j0 : ℕ
  logFiveDepth_le : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0
  weightLength_ge_depth : 10 * j0 + 20 ≤ D.host.Lw

  logDerivativeAtOne : ℝ
  logDerivative_at_one_eq : logDerivativeAtOne = dlogL D 1

  split_tie : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound

  o_tie : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100)
  QS_tie : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100)

  NuLat : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V

  de2 : ℝ
  thickDensity_pos : 0 < de2
  thickDensity_le_one : de2 ≤ 1

  typeDensity_eq_card_div : de2 = (D.host.T2.card : ℝ) / D.R.n

  LaG : ℝ

  Sc : ℝ
  etaSz : ℝ
  Sc_pos : 0 < Sc

  Sc_eq : Sc = (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))

  Cc : ℝ
  win_thick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
    sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + etaSz + 1
  win_top : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
    (bT t : ℝ) + sc.b' / sc.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + sc.b' / sc.x + etaSz
  win_thin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
    sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + etaSz
  cloud_gap : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    Sc ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
    (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * Sc
  cloud_v : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ Sc
  cloud_u : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
    0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ Sc
  be_close : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ etaSz
  etaSz_pos : 0 < etaSz

  TTw : D.what₂.places.Pl → Finset D.host.TT

  TTw_full : ∀ w, (D.host.cls (D.what₂.places.resChar w) = .signal ∨ sc.X' ≤ (D.what₂.places.resChar w : ℝ)) →
    TTw w = Finset.univ

  Ct : ℝ
  t_win : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct

  CGam : ℝ
  CGam_pos : 0 < CGam
  Gam_eq : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L

  wPart : ℕ → D.host.TT → ℕ → ℕ → ℝ

  wPart_ge : ∀ j t p i, 1 ≤ wPart j t p i

  lenMN : D.what₂.Word → D.what₂.places.Pl → ℚ

namespace SizeData₂

def AdmT {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (T : ℕ) : Prop :=
  letI := D.host.cmStar
  T.Prime ∧
  (D.mem u).A.Tstar ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((D.R.f : ℝ) * D.R.k)) * (D.mem u).A.Tstar ∧
  (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (T : D.host.E) ∧
    (π - 1) ∈ Ideal.span {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}) ∧
  T ≠ D.host.pde ∧ T ≠ D.host.pde'

def dZ0 {D : D7} (_L : SizeData₂ D) (j : ℕ) : ℕ := Module.finrank ℂ (D.what₂.Zj D.what₂.mu0 j)

def zeroSpaceRankAtPlace {D : D7} (_L : SizeData₂ D) (j : ℕ) (w : D.what₂.places.Pl) : ℕ :=
  Module.finrank ℂ (D.what₂.Zj (D.what₂.muTw w) j)

def gTypes {D : D7} (_L : SizeData₂ D) : Finset ℕ := {D.host.g 0, D.host.g 1}

variable {D : D7} (L : SizeData₂ D)

def lwP (w : D.what₂.places.Pl) : ℝ := lw D.what₂.LL (D.plEq w)

def sz (w : D.what₂.places.Pl) (y : ℝ) : ℝ :=
  2 * lwP w * ((D.what₂.places.ramIdx w : ℝ) * y)

def lifts (D : D7) : Finset ℕ := Finset.Icc 1 D.R.m

open Classical in

def gainD (j : ℕ) (w : D.what₂.places.Pl) : ℝ :=
  if D.what₂.places.resChar w ∈ L.drop then 0 else L.gain j w

def sg (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  ∑ j ∈ lifts D, (L.gainD j w + L.F j w - L.E u j w)

def Fo : ℝ := ∑ j ∈ lifts D, ∑ w ∈ L.supp, sz w (L.F j w)

def Ga : ℝ := ∑ w ∈ L.supp, sz w ((∑ j ∈ lifts D, L.gainD j w) - L.tau w)

def Ee (u : D.what₂.Word) : ℝ := ∑ j ∈ lifts D, ∑ w ∈ L.supp, sz w (L.E u j w)

def logOm : ℝ := Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - L.logDerivativeAtOne

def La : ℝ := Real.log (L.sc.a * D.host.rdE)

def B0 : ℝ := sizeBudget D.R L.sc.x L.sc.eps

def Nc : ℝ := budgetNc D.R L.sc.x L.sc.eps D.host.T2.card

def MAIN (u : D.what₂.Word) : ℝ :=
  ∑ t : D.host.TT, ((D.R.m : ℝ) * (phF (L.aT t) - (L.aT t : ℝ) * L.logOm) -
    (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ))

def NuH (u : D.what₂.Word) : HLat D.what₂.LL := { D.div.Nu u with L := L.NuLat u }

def VV (l : ℕ) : ℚ := ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e

def vonMangoldtClassSum (j : ℕ) (t : D.host.TT) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Nat.log p (L.aT t).toNat + 2),
    if Odd i then max 0 ((L.aT t : ℝ) / (p : ℝ) ^ i - L.wPart j t p i) else 0

def EtaSupp : Prop := ∀ j w, 1 ≤ j → j ≤ D.R.m → w ∉ L.supp → D.what₂.etaJ j w = 0

def ZeroAbove : Prop := ∀ u, ∀ j ∈ lifts D, ∀ w, L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ) →
  D.what₂.places.resChar w ≠ (D.mem u).A.T →
  D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
  D.what₂.places.resChar w ≠ D.host.d → ¬ D.what₂.places.resChar w ∣ (D.mem u).C.DGam →
  L.gain j w = 0 ∧ L.E u j w = 0

def TuGe : Prop := ∀ u, L.sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ)

end SizeData₂

structure Fam (eps : ℝ) where
  D : ℝ → D7
  L : ∀ x, SizeData₂ (D x)

  x1 : ℝ
  one_lt_family_threshold : 1 < x1
  L_x : ∀ x, x1 < x → (L x).sc.x = x
  L_eps : ∀ x, (L x).sc.eps = eps

def FactEtaMean : Prop := ∀ (D : D7) [IsGalois ℚ D.what₂.LL] (l : ℕ), l.Prime →
  ∀ S : Finset D.what₂.places.Pl, (∀ w, w ∈ S ↔ D.what₂.places.resChar w = l) →
    ∑ w ∈ S, lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ) = Real.log l

def FactLpF : Prop := ∀ (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) →
  0 ≤ lpF l d Ds ∧ lpF l d Ds ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s)

end Formalism.BasicNotions

end
