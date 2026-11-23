import Mathlib
import Formalism.LocalToGlobal.Divisibility.Inputs
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
import Formalism.GaussJetBounds.ThmAEntryFull
import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

def EmbAt {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]) : Prop :=
  ∀ a : K, a ≠ 0 → ‖ι a‖ = ‖(l : ℂ_[l])‖ ^ ((vw w a : ℝ) / (ramw w : ℝ))

structure OrbSys (k : Type) [NormedField k] where

  ι : Type

  σ : Type

  g : ι → MvPowerSeries ι k

  E : MvPowerSeries ι k

  P : MvPolynomial ι (MvPolynomial σ k)

def OrbSys.mul {k : Type} [NormedField k] (S₁ S₂ : OrbSys k) : OrbSys k where
  ι := S₁.ι ⊕ S₂.ι
  σ := S₁.σ ⊕ S₂.σ
  g := Sum.elim (fun x => serAlong Sum.inl (S₁.g x)) (fun x => serAlong Sum.inr (S₂.g x))
  E := serAlong Sum.inl S₁.E * serAlong Sum.inr S₂.E
  P := opAlong Sum.inl Sum.inl S₁.P * opAlong Sum.inr Sum.inr S₂.P

def OrbSys.jet {k : Type} [NormedField k] (S : OrbSys k) (U : MvPowerSeries S.ι k) : MvPolynomial S.σ k :=
  jetPairPoly S.P (MvPowerSeries.subst S.g U * S.E)

def sysA (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l]) (ε : ℂ_[l]) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1) : OrbSys ℂ_[l] where
  ι := ZV d N0 N1
  σ := ZMod d × Fin N0 × Fin N0
  g := g
  E := Formalism.DworkPowerSeriesWeights.mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → ℂ_[l]) be)
  P := ∏ s : ZMod d, minorProd
        (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
            MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l])))
        (p s) (hp s) (I s)

def expA (l d N0 N1 : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) : ℝ :=
  (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
    Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
    ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1)

def sysB (l : ℕ) [Fact l.Prime] (N0 N1 C : ℕ) (be : MvPowerSeries (ZMod 2) ℂ_[l]) (ep : ℂ_[l])
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]) (sgn : ℂ_[l])
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) : OrbSys ℂ_[l] where
  ι := Fin N0 × Fin N1
  σ := Fin N0 × Fin N0
  g := g
  E := Formalism.DworkPowerSeriesWeights.mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
        (fun s : ZMod 2 => (if s = 0 then (1 : ℂ_[l]) else ep) •
          (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) be)
  P := minorProd
        (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (i, a)) * MvPolynomial.X (a, b) :
            MvPolynomial (Fin N0 × Fin N1) (MvPolynomial (Fin N0 × Fin N0) ℂ_[l]))) p hp I

def expB (l N0 N1 C : ℕ) (p : Fin C → ℕ) : ℝ :=
  rho l * ((∑ c, p c : ℕ) : ℝ) - ((N0 : ℝ) * N1) * (Real.logb l (C : ℝ) + 1)

def KnownOk (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) : Prop :=
  ∀ (S : OrbSys ℂ_[l]) (β : ℝ), Q S β → Finite S.ι ∧ (∀ x, MvPowerSeries.constantCoeff (S.g x) = 0) ∧
    HasJetBound S.g S.E S.P (‖(l : ℂ_[l])‖ ^ β)

def noQ (l : ℕ) [Fact l.Prime] : OrbSys ℂ_[l] → ℝ → Prop := fun _ _ => False

inductive IsSys7 (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) : OrbSys ℂ_[l] → ℝ → Prop
  | caseA (d N0 N1 : ℕ) [NeZero d] (h3 : 3 ≤ l) (h2 : 2 ≤ d) (he : Even d) (hN0 : 0 < N0) (K0 : Subfield ℂ_[l])
      (hK : Unram l K0) (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) (be : MvPowerSeries (ZMod d) ℂ_[l])
      (hb : BHyp l d K0 ζ be) (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (ε : ℂ_[l]) (hε : ε = 1 ∨ ε = -1)
      (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
      (nu1 nu2 size : ZMod d → ℕ) (h1 : ∀ s, nu1 s = colN s)
      (h22 : ∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card)
      (hs : ∀ s, size s = ∑ c, p s c)
      (hJ : ∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0) :
      IsSys7 l Q (sysA l d N0 N1 be g ε colN p hp I) (expA l d N0 N1 TT nu1 nu2 size)
  | caseB (N0 N1 C : ℕ) (h3 : 3 ≤ l)
      (K0 : Subfield ℂ_[l]) (hK : Unram l K0) (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
      (be : MvPowerSeries (ZMod 2) ℂ_[l]) (hb : BHyp l 2 K0 ζ be) (ep : ℂ_[l]) (hep : ‖ep‖ = 1)
      (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (sgn : ℂ_[l]) (hsg : sgn = 1 ∨ sgn = -1)
      (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
      IsSys7 l Q (sysB l N0 N1 C be ep g sgn p hp I) (expB l N0 N1 C p)
  | quoted (S : OrbSys ℂ_[l]) (β : ℝ) (h : Q S β) : IsSys7 l Q S β
  | mul {S₁ S₂ : OrbSys ℂ_[l]} {β₁ β₂ : ℝ} (h₁ : IsSys7 l Q S₁ β₁) (h₂ : IsSys7 l Q S₂ β₂) :
      IsSys7 l Q (S₁.mul S₂) (β₁ + β₂)

def MonInt {k : Type} [NormedField k] {σ : Type} (δ : MvPolynomial σ k →ₗ[k] k) : Prop :=
  ∀ n : σ →₀ ℕ, ‖δ (MvPolynomial.monomial n 1)‖ ≤ 1

inductive IsEntry7 (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) : ℝ → ℂ_[l] → Prop
  | gauss (S : OrbSys ℂ_[l]) (β : ℝ) (hS : IsSys7 l Q S β) (U : MvPowerSeries S.ι ℂ_[l]) (hU : Integral U)
      (δ : MvPolynomial S.σ ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l]) (hδ : MonInt δ) : IsEntry7 l Q β (δ (S.jet U))
  | weyl (d N0 N1 : ℕ) [NeZero d] (h3 : 3 ≤ l) (h2 : 2 ≤ d) (he : Even d) (hN0 : 0 < N0) (K0 : Subfield ℂ_[l])
      (hK : Unram l K0) (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) (be : MvPowerSeries (ZMod d) ℂ_[l])
      (hb : BHyp l d K0 ζ be) (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (U : MvPowerSeries (ZV d N0 N1) ℂ_[l]) (hU : Integral U)
      (ε : ℂ_[l]) (hε : ε = 1 ∨ ε = -1)
      (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
      (nu1 nu2 size : ZMod d → ℕ) (h1 : ∀ s, nu1 s = colN s)
      (h22 : ∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card)
      (hs : ∀ s, size s = ∑ c, p s c)
      (hJ : ∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsEntry7 l Q (expA l d N0 N1 TT nu1 nu2 size) (δ (frameJet colN p hp I (thetaZ g U ε be)))

structure PathData (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (J A B : Type) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] where

  Pi : Type

  fPi : Fintype Pi

  x : Pi → Module.Dual K A

  y : Pi → Module.Dual K B

  r : Pi → ℂ_[l]

  gam : Pi → J → ℕ

  gamP : Pi → ℕ

  eps : Pi → J → ℂ_[l]

  e : Pi → J → ℂ_[l]

attribute [instance] PathData.fPi

section Paths

variable {K : Type} [Field K] {l : ℕ} [Fact l.Prime] {J A B : Type} [Fintype J] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

def PathData.val (X : PathData K l J A B) (ι : K →+* ℂ_[l]) (φ : A) (F : B) : ℂ_[l] :=
  ∑ π : X.Pi, (ι (X.x π φ) * (∏ j : J, (((X.gam π j : ℕ) : ℂ_[l])⁻¹ * X.eps π j * X.e π j)) * X.r π *
    (((X.gamP π : ℕ) : ℂ_[l])⁻¹ * ι (X.y π F)))

def IsExpansion (X : PathData K l J A B) (ι : K →+* ℂ_[l]) (Pt : A →ₗ[K] Module.Dual K B) (NA : Set A) (NB : Set B) : Prop :=
  ∀ φ ∈ NA, ∀ F ∈ NB, ι (Pt φ F) = X.val ι φ F

def LastInt (X : PathData K l J A B) : Prop := ∀ π, ‖X.r π‖ ≤ 1

def UnitsInt (X : PathData K l J A B) : Prop := ∀ π j, ‖X.eps π j‖ ≤ 1

def StabDvd (X : PathData K l J A B) (D : ℕ) (j1 : J) : Prop :=
  D ≠ 0 ∧ (∀ π j, X.gam π j ∣ D) ∧ (∀ π, X.gamP π ∣ D) ∧ ∀ π, X.gam π j1 = 1

def EntriesA (Q : OrbSys ℂ_[l] → ℝ → Prop) (X : PathData K l J A B) (s : J → ℝ) : Prop :=
  ∀ π j, ∃ β : ℝ, s j ≤ β ∧ IsEntry7 l Q β (X.e π j)

end Paths

section PathsW

variable {K : Type} [Field K] [NumberField K] [StarRing K] {l : ℕ} [Fact l.Prime] {J A B : Type} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B]

def ColsInt (X : PathData K l J A B) (w : HeightOneSpectrum (𝓞 K)) (NA : Set A) : Prop :=
  ∀ π, ∀ φ ∈ NA, X.x π φ = 0 ∨ 0 ≤ vw w (X.x π φ)

def RowsInt (X : PathData K l J A B) (w : HeightOneSpectrum (𝓞 K)) (NB : Set B) : Prop :=
  ∀ π, ∀ F ∈ NB, X.y π F = 0 ∨ 0 ≤ vw w (X.y π F)

end PathsW

def recA (l d N0 N1 : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (k : ℕ) (w : ZMod d → ℝ) : ℝ :=
  (∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s) + Fnum l d (fun s => ((k : ℝ) - 1) * w s) -
    11 / (l : ℝ) * (∑ s : ZMod d, w s) - gam l * (∑ s ∈ TT, (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) -
    ((d : ℝ) * N0 * N1) * (Real.logb l (kaMaxOneLetter d TT nu1 nu2 : ℝ) + 1)

end Formalism.L2.DIV
