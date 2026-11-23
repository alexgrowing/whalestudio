import Mathlib
import Formalism.PeriodIntegrals.SqfLab
import Formalism.PeriodIntegrals.SqfDivDeg

open Polynomial

noncomputable section

namespace PI.SqfDivDeg.W

instance monicFintype (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Fintype {p : (ZMod g)[X] // p.Monic ∧ p.natDegree = n} :=
  Fintype.ofEquiv _ ((monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv).symm

def Mon (g : ℕ) [Fact g.Prime] (n : ℕ) : Finset (ZMod g)[X] :=
  (Finset.univ : Finset {p : (ZMod g)[X] // p.Monic ∧ p.natDegree = n}).map
    (Function.Embedding.subtype _)

theorem mem_Mon {g : ℕ} [Fact g.Prime] {n : ℕ} {p : (ZMod g)[X]} :
    p ∈ Mon g n ↔ p.Monic ∧ p.natDegree = n := by
  simp [Mon]

theorem card_Mon (g : ℕ) [Fact g.Prime] (n : ℕ) : (Mon g n).card = g ^ n := by
  rw [Mon, Finset.card_map, Finset.card_univ,
    Fintype.card_congr ((monicEquivDegreeLT n).trans (degreeLTEquiv (ZMod g) n).toEquiv)]
  simp

open Classical in

def Rt (g : ℕ) [Fact g.Prime] (n : ℕ) : Finset (ZMod g)[X] :=
  (Mon g n).filter (fun p => ∃ x : ZMod g, p.IsRoot x)

def RootDense : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 1 ≤ n → g ^ n ≤ 2 * (Rt g n).card

def MainCount : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime] (a : ℕ), a ≤ r → ∀ T : Finset (ZMod g)[X],
    (∀ f ∈ T, PI.SqfLab.Eiv g r a f) →
      2 * (T.card : ℝ) + ((Rt g a).card : ℝ) * ((Rt g (r - a)).card : ℝ) ≤ 2 * (g : ℝ) ^ r

end PI.SqfDivDeg.W
