import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

open scoped Pointwise

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]

omit [IsScalarTower S F Ω] in

theorem map_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S F) s ∈ monos (S := F) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem mem_chartRing_extend {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing F x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S F) f, map (algebraMap S F) s, e, map_mem_monos hs, hf.map _, hse.map _,
    by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

theorem smul_mem_span_extend {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing F x I) P) : a • y ∈ Submodule.span (chartRing F x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_extend a.2⟩ : chartRing F x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

theorem span_extend_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing F x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing F x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing F x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_extend P a hz
  · exact Submodule.span_mono Submodule.subset_span

theorem SubSystem.extend_twistSys (c : ℤ) : (twistSys S x c).extend F = twistSys F x c := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  change Submodule.span (chartRing F x I) (twistMod S x c I : Set Ω) = twistMod F x c I
  rw [twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_extend_span]

omit [Algebra S F] [IsScalarTower S F Ω] in

theorem SubSystem.extend_twist (Q R : SubSystem S x Ω) :
    (Q.twist R).extend F = (Q.extend F).twist (R.extend F) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change Submodule.span (chartRing F x I) ((Q.twist R).sub I : Set Ω) =
    Submodule.span (chartRing F x I) (R.sub I : Set Ω) * Submodule.span (chartRing F x I) (Q.sub I : Set Ω)
  rw [SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.mul_induction_on (C := fun y =>
      y ∈ Submodule.span (chartRing F x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_
    · intro r hr q hq
      exact Submodule.subset_span (Set.mul_mem_mul hr hq)
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, q, hq, rfl⟩
    exact Submodule.subset_span (Submodule.mul_mem_mul hr hq)

end

end GroundTheory.Heights₂.Heights.Kleiman
