import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GeneratedTwistSysZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace PointGenerated

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem inv_mem_chartRing (hx : IsSubvar x (primeOf (S := k) x) 0) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing k x I) : a⁻¹ ∈ chartRing k x I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set K := (HilbertPoint.affRing k x i).toIntermediateField' (HilbertPoint.isField_affRing hx hxi)

  have h1 : ∀ b ∈ K, b ∈ chartRing k x I := by
    intro b hb
    change b ∈ HilbertPoint.affRing k x i at hb
    rw [HilbertPoint.affRing, ← Algebra.adjoin_range_eq_range_aeval] at hb
    refine Algebra.adjoin_le (S := chartRing k x I) ?_ hb
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X k l, isHomogeneous_X k i, by
      simp [HilbertPoint.aff]⟩

  have h2 : a ∈ K := by
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    have hs0 := eval_ne_zero_of_mem_monos I hs
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have heq : aeval x f / aeval x s =
        aeval (HilbertPoint.aff x i) f / aeval (HilbertPoint.aff x i) s := by
      rw [HilbertPoint.aff_def, aeval_div_of_isHomogeneous hf, aeval_div_of_isHomogeneous hse]
      field_simp
    rw [heq]
    exact div_mem (show _ ∈ HilbertPoint.affRing k x i from ⟨f, rfl⟩)
      (show _ ∈ HilbertPoint.affRing k x i from ⟨s, rfl⟩)
  exact h1 _ (inv_mem h2)

theorem mem_sub_iff_of_subset (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) {I J : Chart x}
    (h : I.1 ⊆ J.1) (y : Ω) : y ∈ Q.sub J ↔ y ∈ Q.sub I := by
  refine ⟨fun hy => ?_, Q.mono I J h y⟩
  obtain ⟨a, ha, hay⟩ := (Q.mem_iff I J h y).mp hy
  have ha0 : (a : Ω) ≠ 0 := by
    intro h0
    apply ha.ne_zero
    exact Subtype.ext h0
  have hy' : y = (⟨(a : Ω)⁻¹, inv_mem_chartRing hx I a.2⟩ : chartRing k x I) • ((a : Ω) • y) := by
    rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  rw [hy']
  exact Submodule.smul_mem _ _ hay

theorem mem_sub_iff (hx : IsSubvar x (primeOf (S := k) x) 0) (Q : LineBundle k x) (I J : Chart x)
    (y : Ω) : y ∈ Q.sub I ↔ y ∈ Q.sub J := by
  let K : Chart x := ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩
  rw [← mem_sub_iff_of_subset hx Q (show I.1 ⊆ K.1 from Finset.subset_union_left),
    mem_sub_iff_of_subset hx Q (show J.1 ⊆ K.1 from Finset.subset_union_right)]

end PointGenerated

theorem PointGenerated.proof : PointGenerated.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q hx I
  have hsecs : ∀ y, y ∈ Q.toSubSystem.secs ↔ y ∈ Q.sub I := by
    intro y
    rw [SubSystem.secs, Submodule.mem_iInf]
    exact ⟨fun h => h I, fun h J => (PointGenerated.mem_sub_iff hx Q I J y).mp h⟩
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    exact (hsecs y).mp hy
  · intro y hy
    exact Submodule.subset_span ((hsecs y).mpr hy)

end

end GroundTheory.Heights₂.Heights.Kleiman
