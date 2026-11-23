import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext.CutA

def CubeOfTwoIdentities : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1)) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2))) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def PhGramG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))

def GramUnitEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      (∑ j, MvPowerSeries.C (hP (de j) (de j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (de j) (de j')).1 (Xv j)) (Xv j') :
        MvPowerSeries (Fin n) ℂ_[p]) = ∑ j, g.phAt (Xv j)

def GramIsoEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (b : Fin r → κ → ℂ_[p] × ℂ_[p]), (∀ e e', hP (b e) (b e') = 0) →
      (∑ j, MvPowerSeries.C (hP (b j) (b j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (b j) (b j')).1 (Xv j)) (Xv j') :
        MvPowerSeries (Fin r) ℂ_[p]) = 0

def PhDualOfGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))) →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e k, b e k ∈ S) →
      (∀ e k, b' e k ∈ S) → DualIso b b' →
      Simeq (g.PhOn (Sum.elim b b')) (g.beSum ι)

def JetsHigh : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (g.jetPh i)

def JetsOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → p ≠ 2 →
    Simeq (g.phAt (g.mulBy (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (g.phAt (Xv ())) →
    IsIntP (g.jetPh 1)

def JetsTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (a b : ℂ_[p]), g.Ok →
    Simeq (g.be (g.mulBy a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) (g.be (Xv 0) (g.mulBy b (Xv 1))) →
    IsIntP ((a - b) * g.jetPh 2)

def BeDiagG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p) (S : Set (ℂ_[p] × ℂ_[p])), g.Ok →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) →
    Simeq (g.phAt (g.mulBy 2 (Xv ())) : MvPowerSeries Unit ℂ_[p]) (MvPowerSeries.C (2 * 2) * g.phAt (Xv ())) →
    (∀ α ∈ S, Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))) →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) →
    (∀ γ ∈ S, Simeq (2 * g.be (Xv ()) (g.mulBy γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (γ.1 + γ.2) * g.be (Xv ()) (Xv ()))) ∧
    Simeq (g.be (Xv ()) (Xv ()) : MvPowerSeries Unit ℂ_[p]) (2 * g.phAt (Xv ()))

end Formalism.MainNotions.Ext.CutA
