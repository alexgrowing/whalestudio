import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FullLevel

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsSympLevel (D : Datum H) {k : Type} [Field k] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) (N : ℕ) (z : kˣ) (ev : D.La → Q) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧
    (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ x : Q, x ^ N = 1 ↔ ∃ a, ev a = x) ∧
    ∀ a b, e N (ev a) (ev b) (z ^ D.EF a b)

def Induces {D : Datum H} (l : Level H) {Q : Type} [Group Q] (etaA eta ev : D.La → Q) : Prop :=
  (∀ a, ev a ^ (l.M' / l.A) = etaA a) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ev a ^ (l.M' / l.M) = eta a

theorem A_dvd_M' (l : Level H) : l.A ∣ l.M' := Nat.dvd_lcm_right _ _

theorem M_dvd_M' (l : Level H) : l.M ∣ l.M' := Nat.dvd_lcm_left _ _

theorem M'_pos (l : Level H) : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

end GlobalTheory.FullLevel
