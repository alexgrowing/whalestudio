import Mathlib

open MeasureTheory DoubleCoset

namespace GlobalTheory.TwistedOperatorMainTheorem

theorem main_thm : ∀ (G : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (m : MeasureTheory.Measure G) [MeasureTheory.Measure.IsHaarMeasure m] (J : Subgroup G), IsOpen (↑J : Set G) → IsCompact (↑J : Set G) → ∀ (ι : Type) [Countable ι] (x : ι → G), Pairwise (Function.onFun Disjoint fun (i : ι) ↦ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → ∀ (F : G → ℂ), (∀ (g j : G), j ∈ J → ∀ j' ∈ J, F (j * g * j') = F g) → (∀ (g : G), F g ≠ (0 : ℂ) → ∃ (i : ι), g ∈ DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) → (Summable fun (i : ι) ↦ MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G)) * ‖F (x i)‖) → MeasureTheory.Integrable F m ∧ HasSum (fun (i : ι) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (x i) (↑J : Set G) (↑J : Set G))) : ℂ) * F (x i)) (∫ (g : G), F g ∂m) ∧ HasSum (fun (c : DoubleCoset.Quotient (↑J : Set G) (↑J : Set G)) ↦ (↑(MeasureTheory.Measure.real m (DoubleCoset.doubleCoset (Quotient.out c) (↑J : Set G) (↑J : Set G))) : ℂ) * F (Quotient.out c)) (∫ (g : G), F g ∂m) := by
  intro G _ _ _ _ _ m _ J hJo hJc ι _ x hdisj F hF hsupp hsum

  have hmeas : ∀ a : G, MeasurableSet (doubleCoset a (J : Set G) J) := fun a =>
    (IsOpen.mul_left hJo).measurableSet
  have hfin : ∀ a : G, m (doubleCoset a (J : Set G) J) < ⊤ := fun a =>
    ((hJc.mul isCompact_singleton).mul hJc).measure_lt_top

  have hconst : ∀ a g, g ∈ doubleCoset a (J : Set G) J → F g = F a := by
    intro a g hg
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_doubleCoset.1 hg
    exact hF a u hu w hw
  have hint : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, F g ∂m =
      (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i) := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => hconst (x i) g hg), setIntegral_const, Complex.real_smul]
  have hnorm : ∀ i, ∫ g in doubleCoset (x i) (J : Set G) J, ‖F g‖ ∂m =
      m.real (doubleCoset (x i) (J : Set G) J) * ‖F (x i)‖ := by
    intro i
    rw [setIntegral_congr_fun (hmeas _) (fun g hg => by rw [hconst (x i) g hg]), setIntegral_const, smul_eq_mul]
  have hon : ∀ i, IntegrableOn F (doubleCoset (x i) (J : Set G) J) m := fun i =>
    (integrableOn_const (hfin (x i)).ne).congr_fun (fun g hg => (hconst (x i) g hg).symm) (hmeas _)

  have hU : IntegrableOn F (⋃ i, doubleCoset (x i) (J : Set G) J) m :=
    integrableOn_iUnion_of_summable_integral_norm hon (by simpa only [hnorm] using hsum)
  have hout : ∀ g, g ∉ ⋃ i, doubleCoset (x i) (J : Set G) J → F g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨i, hi⟩ := hsupp g h
    exact hg (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hsumI : HasSum (fun i => (m.real (doubleCoset (x i) (J : Set G) J) : ℂ) * F (x i)) (∫ g, F g ∂m) := by
    have h := hasSum_integral_iUnion (fun i => hmeas (x i)) hdisj hU
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h
    simp only [hint] at h
    exact h
  refine ⟨hU.integrable_of_forall_notMem_eq_zero hout, hsumI, ?_⟩

  have hinj : Function.Injective (fun i => DoubleCoset.mk J J (x i)) := by
    intro i j hij
    by_contra hne
    have hj : x j ∈ doubleCoset (x i) (J : Set G) J := by
      obtain ⟨u, hu, w, hw, e⟩ := (DoubleCoset.eq J J (x i) (x j)).1 hij
      exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
    exact Set.disjoint_left.1 (hdisj hne) hj (mem_doubleCoset_self J J (x j))
  have hcls : ∀ i, Quotient.out (DoubleCoset.mk J J (x i)) ∈ doubleCoset (x i) (J : Set G) J := by
    intro i
    obtain ⟨u, w, hu, hw, e⟩ := DoubleCoset.mk_out_eq_mul J J (x i)
    exact mem_doubleCoset.2 ⟨u, hu, w, hw, e⟩
  have hzero : ∀ c ∉ Set.range (fun i => DoubleCoset.mk J J (x i)),
      (m.real (doubleCoset (Quotient.out c) (J : Set G) J) : ℂ) * F (Quotient.out c) = 0 := by
    intro c hc
    by_contra h
    obtain ⟨i, hi⟩ := hsupp _ (right_ne_zero_of_mul h)
    refine hc ⟨i, ?_⟩
    show DoubleCoset.mk J J (x i) = c
    rw [← DoubleCoset.out_eq' J J c]
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hi)).symm
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hsumI using 1
  funext i
  show (m.real (doubleCoset (Quotient.out (DoubleCoset.mk J J (x i))) (J : Set G) J) : ℂ) *
      F (Quotient.out (DoubleCoset.mk J J (x i))) = _
  rw [doubleCoset_eq_of_mem (hcls i), hconst (x i) _ (hcls i)]

end GlobalTheory.TwistedOperatorMainTheorem
