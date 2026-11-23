import Formalism.LocalToGlobal.Divisibility.JetBounds.Statement
import Formalism.LocalToGlobal.Divisibility.JetBounds.MinorProductsLattice
import Formalism.GaussJetBounds.FinalB

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

def expD {H : Type} [Fintype H] [DecidableEq H] (TT : Finset H) (nu1 nu2 size : Bool × H → ℕ) : ℝ :=
  -(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
    (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
    (if t ∈ TT then (nu1 (true, t) : ℝ) else 0))

inductive IsEntryAll (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) : ℝ → ℂ_[l] → Prop
  | thmA {β : ℝ} {e : ℂ_[l]} (h : IsEntry7 l Q β e) : IsEntryAll l Q β e
  | weyl (S : OrbSys ℂ_[l]) (β : ℝ) (hS : IsSysW l Q S β) (U : MvPowerSeries S.ι ℂ_[l]) (hU : Integral U) :
      IsEntryAll l Q β (MvPolynomial.coeff 0 (S.jet U))
  | int (ι : Type) (Th : MvPowerSeries ι ℂ_[l]) (hTh : JetsIntegral Th) (P : MvPolynomial ι ℂ_[l])
      (hP : ∀ n, ‖MvPolynomial.coeff n P‖ ≤ 1) : IsEntryAll l Q 0 (jetPair P Th)
  | ramD (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ) (S : ℂ_[l])
      (u : H → ℂ_[l]) (hS : ‖S‖ ≤ ‖(l : ℂ_[l])‖ ^ (-(1 / 2 : ℝ))) (hu : ∀ t, ‖u t‖ ≤ 1)
      (sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[l]) (hsg : JetsIntegral sg)
      (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0) (hht1 : ∀ τ c, 1 ≤ ht τ c) (I : ∀ τ c, Fin (ht τ c) → Fin N1)
      (nu1 nu2 size : Bool × H → ℕ) (h1 : ∀ τ, nu1 τ = colN τ)
      (h2 : ∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card)
      (hs : ∀ τ, size τ = ∑ c, ht τ c)
      (δ : MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l]) (hδ : MonInt δ) :
      IsEntryAll l Q (expD TT nu1 nu2 size)
        (δ (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[l])))
            (ht τ) (hht τ) (I τ))
          (Formalism.DworkPowerSeriesWeights.mvExp ((-S) • ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
                    MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)) * sg)))

def EntriesAll {K : Type} [Field K] {l : ℕ} [Fact l.Prime] {J A B : Type} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (Q : OrbSys ℂ_[l] → ℝ → Prop) (X : PathData K l J A B) (s : J → ℝ) : Prop :=
  ∀ π j, ∃ β : ℝ, s j ≤ β ∧ IsEntryAll l Q β (X.e π j)

def PlaceInputAllEntries {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df1 : DefSide Bs}
    (Q : ∀ (l : ℕ) [Fact l.Prime], OrbSys ℂ_[l] → ℝ → Prop)
    (Dc : DefCols Df1) (u : Dc.Mem) (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ) : Prop :=
  ∃ (l : ℕ) (_ : Fact l.Prime) (ι : K →+* ℂ_[l])
    (X : PathData K l Bs.J (Fin (Dc.a u) → K) (Fin (Df1.nV t) → K)) (D : ℕ) (j1 : Bs.J) (s : Bs.J → ℝ),
    EmbAt w l ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df1.Mt t : Set (Fin (Df1.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df1.Mt t : Set (Fin (Df1.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ EntriesAll (Q l) X s ∧
    sgw ≤ (ramw w : ℝ) * ∑ j, (s j - (padicValNat l D : ℝ))

def EntryAllBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop), KnownOk l Q → ∀ (β : ℝ) (e : ℂ_[l]), IsEntryAll l Q β e → ‖e‖ ≤ ‖(l : ℂ_[l])‖ ^ β

def LocalValuationBoundAllEntries : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df1 : DefSide Bs) (Dc : DefCols Df1) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ)
    (Q : ∀ (l : ℕ) [Fact l.Prime], OrbSys ℂ_[l] → ℝ → Prop), (∀ (l : ℕ) [Fact l.Prime], KnownOk l (Q l)) →
    PlaceInputAllEntries Q Dc u t Nu w sgw → LocalValuationBoundAt Dc u t Nu w sgw

def AtOfA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df1 : DefSide Bs) (Dc : DefCols Df1) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (sgw : ℝ)
    (Q : ∀ (l : ℕ) [Fact l.Prime], OrbSys ℂ_[l] → ℝ → Prop),
    PlaceInputAtEntry Q Dc u t Nu w sgw → PlaceInputAllEntries Q Dc u t Nu w sgw

end Formalism.L2.DIV
