import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.Katz

namespace GlobalTheory.KatzF

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ} {σ : Type}

variable (k) in

def sig : Fr p k →+* Fr p k := (WittVector.FractionRing.frobenius p k : Fr p k →+* Fr p k)

def twist {ι : Type} (μ : ι → MvPowerSeries σ k) : ι → MvPowerSeries σ k :=
  fun i => MvPowerSeries.map (frobenius k p) (μ i)

def powX (R : Type) [CommRing R] (σ : Type) (n : ℕ) : σ → MvPowerSeries σ R := fun i => X i ^ n

def frobS (f : MvPowerSeries (Fin d) (Fr p k)) : MvPowerSeries (Fin d) (Fr p k) :=
  subst (powX (Fr p k) (Fin d) p) (MvPowerSeries.map (sig p k) f)

def IsF {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (F : Mod p h → Mod p h) : Prop :=
  ∀ f : quasiLog p h, ∃ g : quasiLog p h, g.1 = frobS p f.1 ∧
    F (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

def IsPull {e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k}
    (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k) (m : Mod p hν → Mod p hμ) : Prop :=
  ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
    m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

end GlobalTheory.KatzF
