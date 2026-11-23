import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

open scoped Pointwise

noncomputable section

variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

omit [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] in

theorem map_mem_monos_baseChange {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem mem_chartRing_baseChange {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_baseChange hs, hf.map _,
    hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

theorem smul_mem_span_baseChange {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_baseChange a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

theorem span_baseChange_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_baseChange P a hz
  · exact Submodule.span_mono Submodule.subset_span

theorem baseChange_twistSys (c : ℤ) : (twistSys S x c).baseChange O = twistSys O x c := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  change Submodule.span (chartRing O x I) (twistMod S x c I : Set Ω) = twistMod O x c I
  rw [twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_baseChange_span]

omit [Algebra S O] [IsScalarTower S O Ω] in

theorem baseChange_twist (Q R : SubSystem S x Ω) :
    (Q.twist R).baseChange O = (Q.baseChange O).twist (R.baseChange O) := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change Submodule.span (chartRing O x I) ((Q.twist R).sub I : Set Ω) =
    Submodule.span (chartRing O x I) (R.sub I : Set Ω) * Submodule.span (chartRing O x I) (Q.sub I : Set Ω)
  rw [SubSystem.twist_sub_eq_mul_of_line, Submodule.span_mul_span]
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.mul_induction_on (C := fun y =>
      y ∈ Submodule.span (chartRing O x I) ((R.sub I : Set Ω) * (Q.sub I : Set Ω))) hy ?_ ?_
    · intro r hr q hq
      exact Submodule.subset_span (Set.mul_mem_mul hr hq)
    · intro a b ha hb; exact Submodule.add_mem _ ha hb
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, q, hq, rfl⟩
    exact Submodule.subset_span (Submodule.mul_mem_mul hr hq)

theorem baseChange_tensorSub {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub (fun i => (L i).baseChange O) T = (tensorSub L T).baseChange O := by
  have key : ∀ (l : List (Fin n)) (F : SubSystem S x Ω),
      l.foldl (fun G i => G.twist ((L i).baseChange O)) (F.baseChange O) =
        (l.foldl (fun G i => G.twist (L i)) F).baseChange O := by
    intro l
    induction l with
    | nil => intro F; rfl
    | cons a l ih =>
      intro F
      rw [List.foldl_cons, List.foldl_cons, ← baseChange_twist, ih]
  unfold tensorSub
  rw [← baseChange_twistSys (S := S) (O := O) 0]
  exact key _ _

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
