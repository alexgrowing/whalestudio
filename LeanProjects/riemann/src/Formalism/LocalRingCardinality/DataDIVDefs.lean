import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions NumberField IsDedekindDomain

def MramL (D : D7) (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  ((D.fm u).lat 0).L.comap ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL))

def ur (D : D7) (w : D.what₂.places.Pl) (y : ℝ) : ℝ := (D.what₂.places.ramIdx w : ℝ) * y

def Iu (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL :=
  ∏ w ∈ L.supp, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
    (-(⌊ur D w (L.sg u w)⌋))

def NprimeDef (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u, (D.div.Nu u).L = Submodule.span (𝓞 D.what₂.LL)
    {x | ∃ a ∈ Iu D L u, ∃ y ∈ L.NuLat u, x = (a : D.what₂.LL) • y}

def RRDef (D : D7) : Prop :=
  ∀ x : D.div.RR.V, x ∈ D.div.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | D.jEE y ∈ D.what₂.RRset (D.what₂.muAt w)}

def LocLe {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ k) • B

def LocEq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : Prop :=
  LocLe w 0 A B ∧ LocLe w 0 B A

def lenLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥B ⧸ A.comap B.subtype))

def InertK (D : D7) (p : ℕ) : Prop :=
  D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass

def NuDef (D : D7) (L : SizeData₂ D) : Prop :=
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) ∧
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    (D.what₂.places.resChar w ∈ L.drop ∨ ¬ InertK D (D.what₂.places.resChar w)) →
      LocEq (D.plEq w) (L.NuLat u) (MramL D u)) ∧
  (∀ u w, ∀ l : ℕ, lenLoc (D.plEq w) (L.NuLat u) (MramL D u) = l →
    (l : ℝ) = (L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ))

def meanE (D : D7) (g : (D.what₂.LL →+* ℂ) → ℝ) : ℝ :=
  (∑ σ, g σ) / (Module.finrank ℚ D.what₂.LL : ℝ)

def wSz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (((D.hc ρ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) else 0

def srcPar (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k then (D.hcW u τ).u ⟨i, h⟩
  else
    if hb : (i - D.R.k) / (D.R.t + 1) < D.R.m then
      -(D.hcW u τ).e ⟨(i - D.R.k) / (D.R.t + 1), hb⟩ +
        ((D.R.t : ℚ) + 2 - 2 * (((i - D.R.k) % (D.R.t + 1) + 1 : ℕ) : ℚ)) / 2
    else 0

def nuRow (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  ((srcPar D u τ i : ℚ) : ℝ) + wSz D j τ -
    (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2)

def kerPlace (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * L.logOm

def SZbK (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (L.La + (D.host.d : ℝ) ^ C) +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def SZbP (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * L.La

def hExpl (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, SZbK D L C u j) -
    meanE D (fun e => ⨅ σ : Fin D.what₂.Drows, ∑ j ∈ SizeData₂.lifts D, X.logLam j (D.what₂.ft σ) e) -
    meanE D (fun e => Real.log (X.kapR e))

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.MainNotions.G

end Formalism.BasicNotions

end
