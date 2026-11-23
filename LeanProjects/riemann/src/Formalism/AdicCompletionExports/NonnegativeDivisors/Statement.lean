import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.QuotientMetricDivisors.SixthReductionExplicit

noncomputable section

namespace Formalism.AdicCompletionExports.NonnegativeDivisors

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

structure NRec where

  Pl : Type

  supp : Finset Pl

  tw : Pl → Prop

  lwP : Pl → ℝ

  logWeight_nonneg : ∀ w, 0 ≤ lwP w

  ramIdx : Pl → ℕ

  etaJ : ℕ → Pl → ℚ

  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w

  dZ0 : ℕ → ℕ

  m : ℕ

  f : ℕ

  b : ℝ

  L : ℝ

  x : ℝ

  Nc : ℝ

  vvTerm : ℕ → ℝ

namespace NRec

variable (R : NRec)

def lifts : Finset ℕ := Finset.Icc 1 R.m

open Classical in

def etaSum (j : ℕ) : ℝ :=
  ∑ w ∈ R.supp.filter R.tw, R.lwP w * (R.ramIdx w : ℝ) * (R.etaJ j w : ℝ)

def fmbL : ℝ := (R.f : ℝ) * R.m * R.b * R.L

end NRec

def K0 (Cc Ce : ℝ) : ℝ := 4 * Cc * Ce + 48 * Cc + 1

def NonnegativeDivisorCountBoundAt (R : NRec) (K : ℝ) : Prop :=
  Summable R.vvTerm → ∀ j ∈ R.lifts, R.etaSum j ≤ (R.dZ0 j : ℝ) * (K * R.fmbL + ∑' l, R.vvTerm l)

def ExportAt (R : NRec) (SF : Prop) (C : ℝ) : Prop :=
  SF → Summable R.vvTerm → ∀ j ∈ R.lifts,
    R.etaSum j ≤ (R.dZ0 j : ℝ) *
      (C * ((R.f : ℝ) * R.m * R.b * R.L ^ 2 + (Real.log R.x) ^ 2 * R.Nc) + ∑' l, R.vvTerm l)

def NonnegativeDivisorCountBoundFamily {Ix : ℝ → Type} (Rf : ∀ x, Ix x → NRec) (K : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Ix x, NonnegativeDivisorCountBoundAt (Rf x i) K

section Ties

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
  (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
  (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ)

def TieInj : Prop := Set.InjOn ι Tw

def TieLw : Prop := ∀ y ∈ Tw, Formalism.DivisionValues.lw y = R.lwP (ι y)

def TieRam : Prop := ∀ y ∈ Tw, (Formalism.EigenvalueLevelCeiling.ramw y : ℝ) = (R.ramIdx (ι y) : ℝ)

def TieTw : Prop := ∀ y ∈ Tw, ι y ∈ R.supp ∧ R.tw (ι y)

def TieLift : Prop := ∀ j, lift j ∈ R.lifts

def TieEta : Prop := ∀ y ∈ Tw, ∀ j, ((F.etaJ P ψ Zs j (μ y) y : ℚ) : ℝ) = (R.etaJ (lift j) (ι y) : ℝ)

def TieRank : Prop :=
  ∀ j, (R.dZ0 (lift j) : ℝ) = ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0) : ℝ)

structure Ties : Prop where
  inj : TieInj Tw R ι
  lw : TieLw Tw R ι
  ram : TieRam Tw R ι
  tw : TieTw Tw R ι
  lifts : TieLift R lift
  eta : TieEta F P ψ Zs μ Tw R ι lift
  rank : TieRank F P ψ Zs R lift

end Ties

def StatJoint : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
    (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ) (Kc : ℝ),
    Ties F P ψ Zs μ Tw R ι lift → NonnegativeDivisorCountBoundAt R Kc → Summable R.vvTerm →
      InEta F P ψ Zs μ Tw (fun _ => Kc * R.fmbL + ∑' l, R.vvTerm l)

def StatJointExport : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
    (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ) (SF : Prop) (C : ℝ),
    Ties F P ψ Zs μ Tw R ι lift → ExportAt R SF C → SF → Summable R.vvTerm →
      InEta F P ψ Zs μ Tw
        (fun _ => C * ((R.f : ℝ) * R.m * R.b * R.L ^ 2 + (Real.log R.x) ^ 2 * R.Nc) + ∑' l, R.vvTerm l)

def NonnegativeDivisorCountBound : Prop :=
  ∀ (R : NRec) (SF : Prop) (Kc : ℝ), 0 ≤ Kc → 1 ≤ R.L → 0 ≤ R.b → 0 ≤ R.Nc → NonnegativeDivisorCountBoundAt R Kc → ExportAt R SF Kc

def StatComposite : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
    (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ) (Kc eps : ℝ),
    Ties F P ψ Zs μ Tw R ι lift → NonnegativeDivisorCountBoundAt R Kc → Summable R.vvTerm → 0 ≤ Kc →
    1 ≤ R.x → 0 < eps → R.L = R.x ^ eps → R.b = Real.exp R.L → 0 ≤ R.Nc → 1 ≤ (R.f : ℝ) → 1 ≤ (R.m : ℝ) →
    (Real.log R.x) ^ 2 ≤ R.x ^ eps →
    (hV : ∑' l, R.vvTerm l ≤ Real.sqrt R.b) →
      InEta F P ψ Zs μ Tw
        (fun _ => (Kc + 1) * R.x ^ eps * ((R.f : ℝ) * R.m * R.b * R.x ^ eps + R.Nc))

def StatCompositeExport : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K))) (R : NRec)
    (ι : HeightOneSpectrum (𝓞 K) → R.Pl) (lift : J → ℕ) (SF : Prop) (C eps : ℝ),
    Ties F P ψ Zs μ Tw R ι lift → ExportAt R SF C → SF → Summable R.vvTerm → 0 ≤ C →
    1 ≤ R.x → 0 < eps → R.L = R.x ^ eps → R.b = Real.exp R.L → 0 ≤ R.Nc → 1 ≤ (R.f : ℝ) → 1 ≤ (R.m : ℝ) →
    (Real.log R.x) ^ 2 ≤ R.x ^ eps →
    (hV : ∑' l, R.vvTerm l ≤ Real.sqrt R.b) →
      InEta F P ψ Zs μ Tw
        (fun _ => (C + 1) * R.x ^ eps * ((R.f : ℝ) * R.m * R.b * R.x ^ eps + R.Nc))

def StatJointF : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb)
    (μ : HeightOneSpectrum (𝓞 K) → T) (Tw : Finset (HeightOneSpectrum (𝓞 K)))
    {Ix : ℝ → Type} (Rf : ∀ x, Ix x → NRec) (Kc : ℝ), NonnegativeDivisorCountBoundFamily Rf Kc →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Ix x) (ι : HeightOneSpectrum (𝓞 K) → (Rf x i).Pl) (lift : J → ℕ),
      Ties F P ψ Zs μ Tw (Rf x i) ι lift → Summable (Rf x i).vvTerm →
        InEta F P ψ Zs μ Tw (fun _ => Kc * (Rf x i).fmbL + ∑' l, (Rf x i).vvTerm l)

end Formalism.AdicCompletionExports.NonnegativeDivisors
