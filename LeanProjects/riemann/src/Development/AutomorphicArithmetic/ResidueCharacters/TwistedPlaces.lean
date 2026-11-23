import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

section Quant

variable (L : SizeData₂ D)

abbrev large₂ : ℝ := L.sc.L

def hB : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t + 2

def lA : ℝ := LevelStarExponents.lA L

def lStar : ℝ := LevelStarExponents.lStar L

def eP (C : ℝ) (l : ℕ) : ℝ := C * (1 + hB L / l + Real.logb l (hB L))

def wB : ℝ :=
  max (L.sc.w'' D.R.n + L.etaSz) ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)

def eta₃ : ℝ := L.etaSz + D.R.t + 2

def wP : ℝ := wB L + ((D.R.t : ℝ) + 1) / 2

def GP : ℝ := wP L + L.Sc + eta₃ L

def jA (l : ℕ) : ℕ := max 1 ⌈Real.logb ((l : ℝ) - 1) (lA L)⌉₊

end Quant

def ordH (D : D7) (l : ℕ) : ℕ :=
  sInf {o : ℕ | 0 < o ∧ ((l : ZMod (2 ^ (D.R.e + 2))) ^ o = 1 ∨ (l : ZMod (2 ^ (D.R.e + 2))) ^ o = -1)}

def SplitK (D : D7) (l : ℕ) : Prop := D.host.cls l = PrimeClass.splitK

def InertK (D : D7) (l : ℕ) : Prop :=
  D.host.cls l = PrimeClass.signal ∨ D.host.cls l = PrimeClass.inertClass

def gset (D : D7) : Finset ℕ := {D.host.g 0, D.host.g 1}

def nLam (D : D7) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℕ := Formalism.MainNotions.N.locDeg D.host.E lam

def vhE (D : D7) (l : ℕ) : ℝ := (padicValNat l (Formalism.MainNotions.N.hE D.host) : ℝ)

def epsL (l : ℕ) : ℝ := 1 / (l : ℝ) ^ 2

def nuL (D : D7) (l : ℕ) : ℝ :=
  if h : l.Prime then
    haveI := Fact.mk h
    (KStar.Tree.nuOf l (KStar.Tree.cyc l D.host.E D.nd.Om) (D.R.t * D.R.r) : ℝ)
  else 0

theorem nuL_nonneg (D : D7) (l : ℕ) : 0 ≤ nuL D l := by
  unfold nuL; split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

def VVr (D : D7) (l : ℕ) : ℝ := (D.what₂.VV l : ℝ)

def sumOver (D : D7) (l : ℕ) (f : HeightOneSpectrum (𝓞 D.host.E) → ℝ) : ℝ :=
  ∑ᶠ lam ∈ placesOver D.host.E l, f lam

def TwPl (D : D7) (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

def TwLoc (D : D7) (i : D.nd.Loc) : Prop := TwPl D (D.nd.w i)

theorem TwPl.muAt_eq {D : D7} {w : D.what₂.places.Pl} (h : TwPl D w) : D.what₂.muAt w = D.what₂.muTw w :=
  (D.what₂.muAt_or w).resolve_left h

theorem TwPl.twLoc {D : D7} {w : D.what₂.places.Pl} (h : TwPl D w) {j : ℕ} {i : D.nd.Loc}
    (hi : i ∈ D.nd.locs j w) : TwLoc D i := by
  unfold TwLoc
  rw [((D.nd.locs_mem j w i).1 hi).2]
  exact h

structure Tab (L : SizeData₂ D) where
  s : ∀ i : D.nd.Loc, D.nd.X i → ℝ
  len : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℝ
  BB : D.nd.Loc → ℝ
  band : D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → Prop
  exc : Finset ℕ
  gcost : ℕ → ℕ → ℝ
  gs : ℕ → ℕ → ℝ

open Classical in

def etaSum (L : SizeData₂ D) (j : ℕ) : ℝ :=
  ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
    SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

open Classical in

def twAt (L : SizeData₂ D) (l : ℕ) : Finset D.what₂.places.Pl :=
  L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0 ∧ D.what₂.places.resChar w = l)

open Classical in
theorem mem_twAt {L : SizeData₂ D} {l : ℕ} {w : D.what₂.places.Pl} :
    w ∈ twAt L l ↔ w ∈ L.supp ∧ TwPl D w ∧ D.what₂.places.resChar w = l := by
  unfold twAt TwPl
  exact Finset.mem_filter

def etaAt (L : SizeData₂ D) (j l : ℕ) : ℝ :=
  ∑ w ∈ twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

def vvTerm (D : D7) (l : ℕ) : ℝ :=
  if l.Prime then ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ) * Real.log l else 0

def ShaFinOdd (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < D.R.t → Formalism.GaloisCohomology.shaLen (D.nd.ldat p) (e : ℤ) ≠ ⊤

def aux₃ (L : SizeData₂ D) (C : ℝ) : Prop :=
  ShaFinOdd D → Summable (vvTerm D) → ∀ j ∈ SizeData₂.lifts D,
    etaSum L j ≤ (L.dZ0 j : ℝ) *
      (C * ((D.R.f : ℝ) * D.R.m * L.sc.b * (large₂ L) ^ 2 + (Real.log L.sc.x) ^ 2 * L.Nc) +
        ∑' l, vvTerm D l)

section admitted

variable (L : SizeData₂ D) (tb : Tab L) (C : ℝ)

def adm1 (D : D7) : Prop :=
  ∀ i : D.nd.Loc, TwLoc D i → D.nd.l i ∉ gset D →
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i,
      (D.nd.mult i π : ℝ) * ((D.nd.vcc i π : ℝ) + padicValNat (D.nd.l i) D.what₂.restRowsFiniteGroupCard)

def adm2 : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, TwPl D w → D.what₂.places.resChar w ∉ gset D →
    (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (L.zeroSpaceRankAtPlace j w : ℝ)

def adm3 : Prop := ∀ j ∈ SizeData₂.lifts D, ∀ w, TwPl D w → L.zeroSpaceRankAtPlace j w = L.dZ0 j

def ArchimedeanSignatureMatching : Prop :=
  ∀ i : D.nd.Loc, TwLoc D i → D.nd.l i ∉ gset D → ∀ π ∈ D.nd.Zgood i,
    (D.nd.vcc i π : ℝ) ≤ tb.s i π + sumOver D (D.nd.l i) (tb.len i) +
      VVr D (D.nd.l i) + vhE D (D.nd.l i) + tb.BB i + epsL (D.nd.l i)

def adm5 : Prop :=
  ∀ i : D.nd.Loc, TwLoc D i →
    (D.nd.l i ∉ D.host.small ∧ D.nd.l i ≠ D.host.q ∧ D.nd.l i ≠ D.host.d ∧ D.nd.l i ∉ gset D) →
    tb.BB i ≤ C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (large₂ L) ^ 2

def adm6 : Prop :=
  (∀ i : D.nd.Loc, TwLoc D i → ∀ π ∈ D.nd.Zgood i,
    tb.s i π + epsL (D.nd.l i) ≤ nuL D (D.nd.l i) + 2 / (D.nd.l i : ℝ) ^ 2) ∧
  (∀ j ∈ SizeData₂.lifts D, ∀ l ∈ gset D, tb.gs j l + epsL l ≤ 2 / (l : ℝ) ^ 2)

def AtRow {D : D7} (P : ℕ → Prop) (F : D.nd.Loc → ℕ → Prop) : Prop :=
  ∀ i : D.nd.Loc, TwLoc D i → P (D.nd.l i) → F i (D.nd.l i)

def admA : Prop :=
  AtRow (fun l => 5 ≤ l ∧ SplitK D l ∧ ((l : ℝ) ≤ lStar L ∨ l ∈ tb.exc) ∧ l ∉ gset D)
    (fun i l => 2 * sumOver D l (tb.len i) ≤
      sumOver D l (fun lam => (2 * (nLam D lam : ℝ) * D.R.m + 1) * eP L C l))

def admB : Prop :=
  AtRow (fun l => InertK D l ∧ (l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l ∧ l ∉ gset D)
    (fun i l => ∀ lam ∈ placesOver D.host.E l, tb.len i lam ≤
      C * ((nLam D lam : ℝ) + 1) * D.R.r * (hB L / ((l : ℝ) - 1) ^ (jA L l + 1) +
        (GP L + 1) * ((jA L l : ℝ) + 1) + large₂ L))

open Classical in

def flatCD (i : D.nd.Loc) (lam : HeightOneSpectrum (𝓞 D.host.E)) (l : ℕ) : ℝ :=
  (wP L + eta₃ L) / l + L.Sc + large₂ L + eta₃ L * (if tb.band i lam then 1 else 0)

def MediumInertPrimeLengthBound : Prop :=
  AtRow (fun l => InertK D l ∧ lA L ≤ l ∧ ((l : ℝ) ≤ lStar L ∨ l ∈ tb.exc) ∧ l ∉ gset D)
    (fun i l => ∀ lam ∈ placesOver D.host.E l, tb.len i lam ≤
      C * ((nLam D lam : ℝ) + 1) * D.R.r * (hB L / (l : ℝ) ^ 2 + flatCD L tb i lam l) +
        C * (nLam D lam : ℝ) * D.R.m * eP L C l)

def SmallInertPrimeSmallOrderLengthBound : Prop :=
  AtRow (fun l => InertK D l ∧ (l : ℝ) < lA L ∧ ordH D l ≤ 4 * D.host.Lw ∧ l ∉ gset D)
    (fun i l => ∀ lam ∈ placesOver D.host.E l, tb.len i lam ≤
      C * ((nLam D lam : ℝ) + 1) * D.R.r * (hB L / (l : ℝ) ^ 2) +
        C * ((nLam D lam : ℝ) + 1) * D.R.r * flatCD L tb i lam l +
        C * (nLam D lam : ℝ) * D.R.m * eP L C l)

def BandPlaceWeightApproximation : Prop :=
  ∀ i lam, TwLoc D i → tb.band i lam → ∀ l, lam ∈ placesOver D.host.E l → l.Prime →
    ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ wB L ∧
      |(l : ℝ) * s - L.sc.b| ≤ C * (l * eta₃ L + l * L.Sc + L.sc.b / l + s + l * large₂ L)

def LargePrimeLengthVanishing : Prop :=
  AtRow (fun l => lStar L < l ∧ l ∉ gset D ∧ l ∉ tb.exc)
    (fun i l => (∀ lam ∈ placesOver D.host.E l, tb.len i lam = 0) ∧ tb.BB i = 0) ∧
  (tb.exc.card : ℝ) ≤ ((D.host.TT.card : ℝ) + 2) *
    (L.Sc + 3 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 9)

def ExceptionalPrimesBounded : Prop := ∀ l ∈ tb.exc, (l : ℝ) ≤ 3 * L.sc.b

def SmallPrimeLengthBound : Prop :=
  AtRow (fun l => l ∈ D.host.small ∨ l = 3)
    (fun i l => sumOver D l (tb.len i) + tb.BB i ≤
      C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2)

def midG (l : ℕ) : ℝ :=
  C * D.R.f * (D.R.r * (L.sc.b / l + L.Sc + D.R.t + L.etaSz + large₂ L) + D.R.m * L.sc.b) +
    C * ((D.R.f : ℝ) * D.R.r * D.R.t) ^ C * large₂ L

def RamifiedPrimeLengthBound : Prop :=
  AtRow (fun l => l = D.host.q ∨ l = D.host.d)
    (fun i l => sumOver D l (tb.len i) + tb.BB i ≤ midG L C l) ∧
  ∀ l, (l = D.host.q ∨ l = D.host.d) → midG L C l ≤ 2 * C * D.R.f * D.R.m * L.sc.b

def GeneratorPrimeEtaBound : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ l ∈ gset D,
    etaAt L j l ≤ Real.log l * (L.dZ0 j : ℝ) *
      (tb.gcost j l + tb.gs j l + VVr D l + vhE D l + epsL l) ∧
    tb.gcost j l ≤ C * L.sc.x ^ C * L.etaSz

def TwistedWeightMeanBound : Prop :=
  ∀ l : ℕ, l.Prime → ∑ w ∈ twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log l

def ParametersPolynomiallyBounded (P : ParameterChoice' D L) : Prop :=

  P.CLw ≤ C ∧ P.CYL ≤ C ∧

  (D.R.k : ℝ) ≤ L.sc.x ^ C ∧ (D.R.n : ℝ) ≤ L.sc.x ^ C ∧ (D.R.t : ℝ) ≤ L.sc.x ^ C ∧

  L.sc.x ^ (-L.sc.eps) ≤ L.de2 ∧

  Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ C * L.sc.x ^ C ∧
  Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) ≤ C * L.sc.x ^ C * large₂ L

def AdmT (P : ParameterChoice' D L) : Prop :=
  adm1 D ∧ adm2 L ∧ adm3 L ∧ ArchimedeanSignatureMatching L tb ∧ adm5 L tb C ∧ adm6 L tb ∧
  admA L tb C ∧ admB L tb C ∧ MediumInertPrimeLengthBound L tb C ∧ SmallInertPrimeSmallOrderLengthBound L tb C ∧ BandPlaceWeightApproximation L tb C ∧ LargePrimeLengthVanishing L tb ∧ ExceptionalPrimesBounded L tb ∧
  SmallPrimeLengthBound L tb C ∧ RamifiedPrimeLengthBound L tb C ∧ GeneratorPrimeEtaBound L tb C ∧ ParametersPolynomiallyBounded L C P

end admitted

theorem liesOver_resChar (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq w).asIdeal.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)}) := by
  have hl : (D.what₂.places.resChar w).Prime := D.what₂.places.resChar_prime w
  have hl0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hl0] at h1
  have h2 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    exact_mod_cast h1
  have h3 : 0 < vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [h2]; exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) =
      algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) := by simp
  have h4 : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) < 1 := by
    rcases lt_or_eq_of_le ((D.plEq w).valuation_le_one (K := D.what₂.LL)
      ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) with h | h
    · exact h
    · exfalso
      unfold vAdd at h3
      rw [hc, h] at h3
      simp at h3
  have h5 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal :=
    ((D.plEq w).valuation_lt_one_iff_mem _).1 h4
  have : Fact (D.what₂.places.resChar w).Prime := ⟨hl⟩
  have hmax := Int.ideal_span_isMaximal_of_prime (D.what₂.places.resChar w)
  have := (D.plEq w).isPrime
  constructor
  apply hmax.eq_of_le (Ideal.IsPrime.under ℤ (D.plEq w).asIdeal).ne_top
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
  simpa using h5

theorem admissibleMeanCondition_holds (L : SizeData₂ D) : TwistedWeightMeanBound L := by
  classical
  intro l hl
  have : Fact l.Prime := ⟨hl⟩
  have hmax := Int.ideal_span_isMaximal_of_prime l
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 D.what₂.LL)
  rw [RingOfIntegers.rank] at hsum
  have hsum' : ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.what₂.LL)).toFinset,
      q.ramificationIdx ℤ * q.inertiaDeg ℤ = Module.finrank ℚ D.what₂.LL := by
    rw [← hsum]
    exact (Finset.sum_set_coe (f := fun q : Ideal (𝓞 D.what₂.LL) => q.ramificationIdx ℤ * q.inertiaDeg ℤ) _).symm
  have hn : (0 : ℝ) < (Module.finrank ℚ D.what₂.LL : ℝ) := by exact_mod_cast Module.finrank_pos
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_natCast_nonneg l
  set G : Ideal (𝓞 D.what₂.LL) → ℝ := fun q =>
    Real.log l * ((q.ramificationIdx ℤ * q.inertiaDeg ℤ : ℕ) : ℝ) / (Module.finrank ℚ D.what₂.LL : ℝ) with hG
  set S := twAt L l with hS
  have hterm : ∀ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) = G (D.plEq w).asIdeal := by
    intro w hw
    have hwl : D.what₂.places.resChar w = l := (mem_twAt.1 hw).2.2
    have := (D.plEq w).isPrime
    have : (D.plEq w).asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := hwl ▸ liesOver_resChar D w
    have hN := Ideal.pow_inertiaDeg l (D.plEq w).asIdeal
    simp only [hG, SizeData₂.lwP, lw, D.ram_eq w, eWL, ← hN]
    push_cast
    rw [Real.log_pow]
    ring
  have hinj : Set.InjOn (fun w => (D.plEq w).asIdeal) (S : Set D.what₂.places.Pl) := by
    intro a _ b _ hab
    exact D.plEq.injective (HeightOneSpectrum.ext hab)
  calc ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)
      = ∑ w ∈ S, G (D.plEq w).asIdeal := Finset.sum_congr rfl hterm
    _ = ∑ q ∈ S.image (fun w => (D.plEq w).asIdeal), G q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.what₂.LL)).toFinset, G q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hq
          have hwl : D.what₂.places.resChar w = l := (mem_twAt.1 hw).2.2
          rw [Set.mem_toFinset]
          exact ⟨(D.plEq w).isPrime, hwl ▸ liesOver_resChar D w⟩
        · intro q _ _
          simp only [hG]
          positivity
    _ = Real.log l := by
        simp only [hG]
        rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, hsum']
        field_simp

def admitted (L : SizeData₂ D) (P : ParameterChoice' D L) (C : ℝ) : Prop := ShaFinOdd D → ∃ tb : Tab L, AdmT L tb C P

def Stmt (L : SizeData₂ D) (P : ParameterChoice' D L) (Ca C : ℝ) : Prop := admitted L P Ca → aux₃ L C

end Formalism.MainNotions.TwistedPlaces

end
