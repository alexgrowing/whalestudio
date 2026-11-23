import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace GlobalTheory.ThStr

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField Classical

variable {l : ℕ} [Fact l.Prime]

def laS (l : ℕ) [Fact l.Prime] (d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) ℂ_[l] :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : ℂ_[l]) ^ e)⁻¹ else 0

def laAt {d : ℕ} {κ : Type} (ι : ZMod d → κ) (s : ZMod d) : MvPowerSeries κ ℂ_[l] :=
  MvPowerSeries.subst (fun r : ZMod d => (MvPowerSeries.X (ι r) : MvPowerSeries κ ℂ_[l])) (laS l d s)

def parDeg {d : ℕ} (par : Bool) (n : ZMod d →₀ ℕ) : ℕ :=
  n.sum fun s k => if decide (Even s.val) = par then k else 0

def cobdry {d : ℕ} (par : Bool) (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (Bool × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (false, r)) s + laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])
      else laAt (fun r => (false, r)) s) be -
    MvPowerSeries.subst (fun s : ZMod d => (laAt (fun r => (false, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l])) be -
    MvPowerSeries.subst (fun s : ZMod d => if decide (Even s.val) = par then
      (laAt (fun r => (true, r)) s : MvPowerSeries (Bool × ZMod d) ℂ_[l]) else laAt (fun r => (false, r)) s) be

structure IsBe (d : ℕ) (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop where
  coef : CoefWf be
  inv : ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) be = be
  bideg : ∀ n, MvPowerSeries.coeff n be ≠ 0 →
    parDeg true n ≠ 0 ∧ parDeg false n ≠ 0 ∧ ¬ (parDeg true n = 1 ∧ parDeg false n = 1)
  cob : ∀ par, IntegralW (expMv (cobdry par be))

def FormA {d : ℕ} {V A B : Type} [Fintype V] [Fintype A] [Fintype B] (be : V → MvPowerSeries (ZMod d) ℂ_[l])
    (Th : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l]) : Prop :=
  IntegralMv (MvPowerSeries.subst
    (fun k : ZMod d × (V × A × B) => (laAt (fun r => (r, k.2)) k.1 : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l]))
    (Th * expMv (∑ x : V × A × B, MvPowerSeries.subst
      (fun s : ZMod d => (MvPowerSeries.X (s, x) : MvPowerSeries (ZMod d × (V × A × B)) ℂ_[l])) (be x.1))))

def FormB {κ : Type} [Fintype κ] (be : MvPowerSeries (ZMod 2) ℂ_[l]) (Th : MvPowerSeries κ ℂ_[l]) : Prop :=
  IntegralMv (MvPowerSeries.subst
    (fun k : κ => (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l]) (logF l) : MvPowerSeries κ ℂ_[l]))
    (Th * expMv (MvPowerSeries.C (1 / 2 : ℂ_[l]) * ∑ k : κ, MvPowerSeries.subst
      (fun _ : ZMod 2 => (MvPowerSeries.X k : MvPowerSeries κ ℂ_[l])) be)))

def JetInt {κ : Type} (F : MvPowerSeries κ ℂ_[l]) : Prop :=
  ∀ n : κ →₀ ℕ, ‖(n.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff n F‖ ≤ 1

def StrA (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → InertK D p → AllSplit D p →
    ∃ ep : ℂ_[p], ep ∈ Wp p ∧ ‖ep‖ = 1 ∧ ∀ (d : ℕ) [NeZero d] (Po : Pos D p d),
      ∃ be : {v // v ∈ Po.V} → MvPowerSeries (ZMod d) ℂ_[p], (∀ v, IsBe d (be v)) ∧
        ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
          (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E) (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E),
          admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
          (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
          ∀ F, IsComb D T e lam L L' F →
            FormA be (atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => MvPowerSeries.X j) F)

def StrB (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → InertK D p → IsFrobC D p →
    ∃ ep : ℂ_[p], ep ∈ Wp p ∧ ‖ep‖ = 1 ∧ ∃ be : MvPowerSeries (ZMod 2) ℂ_[p], IsBe 2 be ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → (∀ τ, OrthoBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, OrthoBasisW D (tauEmb D lam τ) L' (P' τ)) →
        ∀ F, IsComb D T e lam L L' F →
          FormB be (atLin (fun k j => ep * chgB D lam P P' k j) (fun j => MvPowerSeries.X j) F)

def beTil {d : ℕ} [NeZero d] {ρ : Type} [Fintype ρ] (b0 : MvPowerSeries (Fin 2) ℂ_[l]) (Ni Ni' : ρ → ZMod d → ℂ_[l]) :
    MvPowerSeries (ZMod d) ℂ_[l] :=
  ∑ r : ρ, MvPowerSeries.subst (fun i : Fin 2 => ∑ s : ZMod d,
    (MvPowerSeries.C (if i = 0 then (if Even s.val then Ni r s else 0) else (if Even s.val then 0 else Ni' r s)) *
      MvPowerSeries.X s : MvPowerSeries (ZMod d) ℂ_[l])) b0

def avgT {d : ℕ} (b : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.C (((l ^ d - 1 : ℕ) : ℂ_[l])⁻¹) * ∑ u ∈ Polynomial.nthRootsFinset (l ^ d - 1) (1 : ℂ_[l]),
    MvPowerSeries.rescale (fun s : ZMod d => if Even s.val then u ^ (l ^ s.val) else (u ^ (l ^ s.val))⁻¹) b

def inT {d : ℕ} (b : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun s : ZMod d => laS l d s) b

end GlobalTheory.ThStr
