import Formalism.GaussJetBounds.Statement

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def PureFormula : Prop :=
  ∀ (K : Type u) [Field K] (l d N0 N1 : ℕ) [NeZero d], 2 ≤ l →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K),
      (∀ x i, M x i ≠ 0 → lt i = x.1) →
    ∀ be : MvPowerSeries (ZMod d) K, ∀ (i j : ι) (α β : ℕ), lt i ≠ lt j →
      MvPowerSeries.coeff (pureMon l i j α β) (bSum M be) =
        MvPowerSeries.coeff (Finsupp.single (lt i) (l ^ α) + Finsupp.single (lt j) (l ^ β)) be *
          ∑ ab : Fin N0 × Fin N1, M (lt i, ab.1, ab.2) i ^ (l ^ α) * M (lt j, ab.1, ab.2) j ^ (l ^ β)

def FrobCong : Prop :=
  ∀ (R : Type u) [CommRing R] (l : ℕ), l.Prime → ∀ (ι : Type v) [Fintype ι] (u w : ι → R)
    (j β : ℕ), ∃ r : R,
      (∑ a, u a ^ (l ^ (j + β)) * w a ^ (l ^ β)) - (∑ a, u a ^ (l ^ j) * w a) ^ (l ^ β) = (l : R) * r

def SpecialIndep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (J : ℕ) (j : Fin J → ℕ), Function.Injective j →
    (Matrix.of fun (i a : Fin J) =>
      (MvPolynomial.X a : MvPolynomial (Fin J) (ZMod l)) ^ (l ^ j i)).det ≠ 0

def SpecialRank : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (T : Type) [Fintype T] [DecidableEq T] (J : T → ℕ)
    (j : ∀ t, Fin (J t) → ℕ), (∀ t, Function.Injective (j t)) → ∀ N0 : ℕ,
    (∑ t, J t) ≤ N0 →
    ∃ f : (Σ t, Fin (J t)) → Fin N0, Function.Injective f ∧
      (Matrix.of fun (r c : Σ t, Fin (J t)) =>
        (MvPolynomial.X (r.1, f c) : MvPolynomial (T × Fin N0) (ZMod l)) ^ (l ^ j r.1 r.2)).det ≠ 0

def MinorDeg : Prop :=
  ∀ (R : Type u) [CommRing R] (m p : ℕ) (top : Fin (p + 1) → R) (T : Fin p → Fin m → R),
    ∀ mono ∈ (Matrix.of fun (i c : Fin (p + 1)) =>
        (Fin.cases (fun c => MvPolynomial.C (top c))
          (fun i' c => ∑ k, MvPolynomial.C (T i' k) * MvPolynomial.X (k, c)) i c :
          MvPolynomial (Fin m × Fin (p + 1)) R)).det.support,
      ∀ k : Fin m, (∑ c : Fin (p + 1), mono (k, c)) ≤ 1

end Formalism.DworkPowerSeriesWeights
