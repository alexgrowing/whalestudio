import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.LocalRingCardinality.DataParams₂

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7)

def vOne (τ : D.what₂.Tau) (l : ℕ) : ℝ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k - 1 then ((D.hc τ).v ⟨l - 1, by omega⟩ : ℝ) else 0

def bOne (τ : D.what₂.Tau) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then ((D.hc τ).b ⟨j - 1, by omega⟩ : ℝ) else 0

def uS (u : D.what₂.Word) (τ : D.what₂.Tau) : Fin D.R.k → ℝ := fun i => ((D.hcW u τ).u i : ℝ)

def uOne (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ D.R.k then uS D u τ ⟨i - 1, by omega⟩ else 0

def IsTop (τ : D.what₂.Tau) : Prop :=
  ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t

def bTop (τ : D.what₂.Tau) : ℝ := -uOne D D.u₀ τ D.R.k

def gg : ℝ := (D.host.g 0 : ℝ) * D.host.g 1

def typedPl : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {p | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}

abbrev SplitsE (p : ℕ) : Prop := SplitsCompl D.host.E p

def VV (τ : D.what₂.Tau) : ℝ := D.dsig τ * ∏ i ∈ Finset.range D.R.r, (i.factorial : ℝ)

def Tcrit (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.host.ka ^ (-(((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2)) *
    D.host.rdE ^ (-(((D.R.m : ℝ) - 1) / 2)) *
    gg D ^ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
    VV D τ / vand (uS D u τ)) ^ ((1 : ℝ) / D.R.k)

def Tr (u : D.what₂.Word) : ℝ := ((D.mem u).A.T : ℝ)

def beUU (κ : ℝ) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (Y : ℝ) : ℝ :=
  beS κ D.R.rS (lamS D.R (D.hc τ)) (Tr D u) (Tr D u') (uS D u τ) (uS D u' τ) Y

def tV (u u' : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  Real.sqrt (Tcrit D u τ * Tcrit D u' τ / (Tr D u * Tr D u'))

open Classical in

def aEff (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  if IsTop D τ then uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) else uOne D u τ 1 - vOne D τ 1

def gaG : ℝ :=
  ∏ᶠ p ∈ typedPl D, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)

open Classical in

def genScal (u u' : D.what₂.Word) : ℝ :=
  (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * gaG D *
    (∑' P : D.s.Pair u u',
      if Formalism.MainNotions.S.scalarP D.s P ∧
          D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0
      then D.s.pval P else 0).re

def hsDiagAllD (u : D.what₂.Word) : ℝ := hsNormSq (KD D u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def f3G : ℝ := ∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))

def IsSat {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) : Prop :=
  Φ = famG D.s ∨ Φ = famNG D.s ∨ Φ = {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} ∨
    Φ = {t | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Line2a : Prop :=
  ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ → Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤ f3G D * gaG D * (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def HostFactorProductPowerIdentity : Prop := f3G D = (∏ i : Fin 2, (1 + 3 / (D.host.g i : ℝ))) ^ D.R.f

def StandingNumericalData (C0 : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ u (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ u τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ u τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  (∀ u u', u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) ∧
  (∀ u, SplitsE D (D.mem u).A.T ∧
    (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 % (D.host.g 0 * D.host.g 1) ^ 2) ∧
  (∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ) ∧
    (D.duS u : ℝ) ≤ (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0) ∧
  SplitsE D (D.host.g 0) ∧ SplitsE D (D.host.g 1) ∧

  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ u, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)

def StandingHypotheses (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let L : ℝ := large₂.sc.L
  let b : ℝ := large₂.sc.b
  let Del : ℝ := D.s.Del
  let g1 : ℝ := D.host.g 0
  let g2 : ℝ := D.host.g 1
  8 * large₂.CGam ≤ C' ∧ C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (k * b) ^ 8 ≤ g1 ∧ g1 ≤ b ^ Cg ∧ (k * b) ^ 8 ≤ g2 ∧ g2 ≤ b ^ Cg ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ u τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  (∀ u, b ^ (cT * m) ≤ Tr D u ∧ Tr D u ≤ b ^ (CT * m)) ∧
  Cl ≤ m ∧ 0 < Cl

open scoped nonZeroDivisors

def eSum (Ce : ℝ) : ℝ :=
  Ce * ∑' p : HeightOneSpectrum (𝓞 D.host.F),
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))

def ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def gE : D.host.E := ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

def IsLatGLOB (L : LatticeDataWithDual D) : Prop :=
  ∀ i s : ℕ,
    L.aaV i s = ddE D ^ (-((2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1)) + 1)) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.aaP i s = ddE D ^ (-(2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1))) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.ρ i s = rhoReal D i s

def IsLocA (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  ∀ τ, (x τ).lam = lamSH D.R (D.hc τ) ∧ (x τ).u = uS D u τ ∧ (x τ).u' = uS D u' τ

def NA : ℝ := 4 * 5 * ((D.R.rS : ℝ) + 1)

def ThA (CA : ℝ) (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) : ℝ :=
  ThS D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L

def IsLocC (u u' : D.what₂.Word) (l : ℕ) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  IsLocA D u u' x ∧ ∀ τ, (x τ).a = 5 / 2 - vOne D τ l ∧ (x τ).b = (D.s.Del : ℝ) / 2 - vOne D τ l ∧
    (x τ).a1 = 5 / 2 - vOne D τ l ∧ (x τ).b1 = NA D ^ 3 - vOne D τ l

end Formalism.MainNotions.S
