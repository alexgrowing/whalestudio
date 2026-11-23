import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def fullSumIrr (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ ∃ μ, (Quot.out q).Mark μ then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

def CompareIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt sel : Polynomial G.F → ℂ), IsSel G sel →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (r : ℕ), 0 < r → ∀ (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
      IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      Match G r K φ K' f' →
      (G.n : ℂ) * markedSumIrr G wt sel L.K.toSubgroup f r K φ = fullSumIrr G wt L.K.toSubgroup f 1 K' f'

end GlobalTheory.LKMid
