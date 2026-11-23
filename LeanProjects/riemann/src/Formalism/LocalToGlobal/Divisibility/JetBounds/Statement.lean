import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

def SysBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop), KnownOk l Q → ∀ (S : OrbSys ℂ_[l]) (β : ℝ), IsSys7 l Q S β →
    HasJetBound S.g S.E S.P (‖(l : ℂ_[l])‖ ^ β)

def EntryBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop), KnownOk l Q → ∀ (β : ℝ) (e : ℂ_[l]), IsEntry7 l Q β e → ‖e‖ ≤ ‖(l : ℂ_[l])‖ ^ β

def EmbLower : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]), EmbAt w l ι → ∀ (a : K) (s : ℝ), a ≠ 0 → ‖ι a‖ ≤ ‖(l : ℂ_[l])‖ ^ s →
      (ramw w : ℝ) * s ≤ (vw w a : ℝ)

def EmbInt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]), EmbAt w l ι → ∀ a : K, (a = 0 ∨ 0 ≤ vw w a) → ‖ι a‖ ≤ 1

def PathBound : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime] (J A B : Type) [Fintype J] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (X : PathData K l J A B) (ι : K →+* ℂ_[l]) (D : ℕ) (j1 : J) (s : J → ℝ) (φ : A) (F : B),
    (∀ π, ‖ι (X.x π φ)‖ ≤ 1) → (∀ π, ‖ι (X.y π F)‖ ≤ 1) → LastInt X → UnitsInt X → StabDvd X D j1 →
    (∀ π j, ‖X.e π j‖ ≤ ‖(l : ℂ_[l])‖ ^ (s j)) →
      ‖X.val ι φ F‖ ≤ ‖(l : ℂ_[l])‖ ^ (∑ j, (s j - (padicValNat l D : ℝ)))

def RecLe : Prop :=
  ∀ (l d N0 N1 : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (k : ℕ) (w E : ZMod d → ℝ), 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      recA l d N0 N1 TT nu1 nu2 size k w ≤ expA l d N0 N1 TT nu1 nu2 size

def RecBLe : Prop :=
  ∀ (l N0 N1 C : ℕ), 3 ≤ l → ∀ (p : Fin C → ℕ) (k : ℕ) (w a : ℝ), (l : ℝ) ≤ a → (C : ℝ) ≤ 2 * a →
    ((k : ℝ) - 1) * w ≤ ((∑ c, p c : ℕ) : ℝ) →
      rho l * (((k : ℝ) - 1) * w) - 3 * ((N0 : ℝ) * N1) * Real.logb l a ≤ expB l N0 N1 C p

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}

def LocalValuationBoundAt (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt t, Dc.Pt u t φ F = 0 ∨ sgw ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def PlaceInputAtEntry (Q : ∀ (l : ℕ) [Fact l.Prime], OrbSys ℂ_[l] → ℝ → Prop) (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∃ (l : ℕ) (_ : Fact l.Prime) (ι : K →+* ℂ_[l])
    (X : PathData K l Bs.J (Fin (Dc.a u) → K) (Fin (Df1.nV t) → K)) (D : ℕ) (j1 : Bs.J) (s : Bs.J → ℝ),
    EmbAt w l ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df1.Mt t : Set (Fin (Df1.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df1.Mt t : Set (Fin (Df1.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ EntriesA (Q l) X s ∧
    sgw ≤ (ramw w : ℝ) * ∑ j, (s j - (padicValNat l D : ℝ))

end Final

def LocalValuationBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df1 : DefSide Bs) (Dc : DefCols Df1) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ)
    (Q : ∀ (l : ℕ) [Fact l.Prime], OrbSys ℂ_[l] → ℝ → Prop), (∀ (l : ℕ) [Fact l.Prime], KnownOk l (Q l)) →
    PlaceInputAtEntry Q Dc u t Nu w sgw → LocalValuationBoundAt Dc u t Nu w sgw

end Formalism.L2.DIV
