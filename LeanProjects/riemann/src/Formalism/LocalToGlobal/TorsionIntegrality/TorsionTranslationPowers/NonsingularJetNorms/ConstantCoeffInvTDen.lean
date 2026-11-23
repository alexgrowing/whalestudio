import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeriesSubgroup

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Shape

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {a | ‖a‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    change ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_ball {K : Type} [NormedField K] [IsUltrametricDist K] {a : K} :
    a ∈ ball K ↔ ‖a‖ ≤ 1 := Iff.rfl

section Alg

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

end Alg

section Pts

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

theorem px_neg (Q : W.toAffine.Point) : px W (-Q) = px W Q := by
  cases Q <;> rfl

end Pts

section Nrm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end Nrm

end Shape

open Shape

theorem XTShape_holds : XTShape := UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds

theorem FacShape_of (hR : IntRules) (hA : UnitAtRules) (hK : UnitKap) (hP : UnitPsi2)
    (hD : UnitDiff) (hX : XTShape) : FacShape := by
  intro K _ _ _ W hW P Q hP0 hQ0 hPx hPy hQx hQy hs hd
  obtain ⟨hI, hc0, hc1, hc2⟩ := hX K W hW P hP0 hPx hPy
  obtain ⟨rC, -, rAdd, rNeg, -⟩ := hR K
  obtain ⟨-, -, rU, -⟩ := hA K
  have hf : IntS (C (px W Q) - xT W P) := by
    rw [sub_eq_add_neg]; exact rAdd _ _ (rC _ hQx) (rNeg _ hI)
  have e0 : coeff 0 (C (px W Q) - xT W P) = px W Q - px W P := by
    rw [map_sub, hc0, coeff_zero_C]
  have e1 : coeff 1 (C (px W Q) - xT W P) = -psi2 W P := by
    rw [map_sub, hc1, coeff_C]; simp
  have hxeq : (P + Q = 0 ∨ P - Q = 0) → px W Q = px W P := by
    rintro (h | h)
    · rw [eq_neg_of_add_eq_zero_left h, px_neg]
    · rw [sub_eq_zero.mp h]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · refine rU 0 _ hf (fun i hi => absurd hi (Nat.not_lt_zero i)) ?_
    rw [e0, norm_sub_rev]
    exact hD K W hW P Q hP0 hQ0 h1 h2 hPx hPy hQx hQy (hs h1) (hd h2)
  · refine rU 1 _ hf (fun i hi => ?_) ?_
    · obtain rfl : i = 0 := by omega
      rw [e0, hxeq h1, sub_self]
    · rw [e1, norm_neg]
      rcases h1 with h | h
      · have hPQ : P = -Q := eq_neg_of_add_eq_zero_left h
        have hPP : P + P = P - Q := by rw [hPQ, sub_eq_add_neg]
        have hne : P + P ≠ 0 := by
          rw [hPQ, ← neg_add]; exact neg_ne_zero.mpr h2
        refine hP K W hW P hP0 hne hPx hPy ?_
        rw [hPP]; exact hd (hPP ▸ hne)
      · have hPQ : P = Q := sub_eq_zero.mp h
        have hne : P + Q ≠ 0 := by rw [hPQ]; exact h2
        have hne' : P + P ≠ 0 := by rw [hPQ]; exact h2
        refine hP K W hW P hP0 hne' hPx hPy ?_
        have := hs hne
        rwa [← hPQ] at this
  · have hPQ : P = Q := sub_eq_zero.mp h1
    obtain ⟨k0, k1⟩ := hK K W hW P hP0 (by rw [hPQ]; exact h2) hPx hPy
    refine rU 2 _ hf (fun i hi => ?_) ?_
    · have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · rw [e0, hPQ, sub_self]
      · rw [e1, k0, neg_zero]
    · rw [map_sub, hc2 k0, coeff_C]
      simpa using k1

end Formalism.L2.Th1.E
