import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

def RegEl (G : HTGroup p) (y : G.Cˣ) : Prop :=
  (minpoly G.F (y : G.C)).natDegree = G.n ∧ (minpoly G.F (y : G.C)).Separable

def pairOf {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

theorem pairOf_β {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).β = F.β := rfl

theorem pairOf_γ {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).γ = (r : G.Cˣ × ℚˣ).1 := rfl

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

example : ∃ (h : RegEl (ex 1 one_ne_zero) exPair.γ),
    pairOf (Form.ofPair exPair) ⟨(exPair.γ, exPair.c), exPair.sim, by show (0:ℚ) < 5; norm_num⟩ h = exPair :=
  ⟨exPair.reg, rfl⟩

end GlobalTheory.LKCx
