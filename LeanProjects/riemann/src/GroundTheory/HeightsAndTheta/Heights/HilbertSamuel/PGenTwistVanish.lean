import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
