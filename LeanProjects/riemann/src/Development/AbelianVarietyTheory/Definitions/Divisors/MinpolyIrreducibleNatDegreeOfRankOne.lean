import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def SeesIrr (G : HTGroup p) (f : G.GAf → ℂ) : Prop :=
  ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf),
    f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 →
      Irreducible (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n

def CxCountIrr : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (wt : Polynomial G.F → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    SeesIrr G f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotal G v wt L.K.toSubgroup f K' f' = fullSumIrr G wt L.K.toSubgroup f 1 K' f'

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSumIrr G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSumIrr, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) : SeesIrr G (fun _ => 0) := fun _ _ _ _ _ _ hf => absurd rfl hf

end GlobalTheory.LKCx
