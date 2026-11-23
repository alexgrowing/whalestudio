import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def CxCountReg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 →
    ∀ (wt : Polynomial G.F → ℂ) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    (∀ g, f g ≠ 0 → RegAf G g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      cxTotal G v wt L.K.toSubgroup f K' f' = fullSum G wt L.K.toSubgroup f 1 K' f'

theorem fullSum_eq_fullSumIrr_of_term_zero (G : HTGroup p) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ)
    (h : ∀ P : Pair G, (∃ μ, P.Mark μ) → ¬ Irreducible P.pol → wt P.pol * P.term Kf f r K φ = 0) :
    fullSum G wt Kf f r K φ = fullSumIrr G wt Kf f r K φ := by
  unfold fullSum fullSumIrr
  refine finsum_congr fun q => ?_
  by_cases hm : ∃ μ, (Quot.out q).Mark μ
  · by_cases hi : Irreducible (Quot.out q).pol
    · rw [if_pos hm, if_pos ⟨hi, hm⟩]
    · rw [if_pos hm, if_neg (fun h' => hi h'.1)]
      exact h _ hm hi
  · rw [if_neg hm, if_neg (fun h' => hm h'.2)]

example (G : HTGroup p) (v wt Kf K' f') :
    cxTotal G v wt Kf (fun _ => 0) K' f' = fullSum G wt Kf (fun _ => 0) 1 K' f' := by
  simp [cxTotal, cxSum, cxSumAt, fullSum, Pair.term, Pair.termAt, pointSum]

example (G : HTGroup p) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) :
    fullSum G (fun _ => 0) Kf f 1 K' f' = fullSumIrr G (fun _ => 0) Kf f 1 K' f' :=
  fullSum_eq_fullSumIrr_of_term_zero G _ Kf f 1 K' f' fun _ _ _ => zero_mul _

end GlobalTheory.LKCx
