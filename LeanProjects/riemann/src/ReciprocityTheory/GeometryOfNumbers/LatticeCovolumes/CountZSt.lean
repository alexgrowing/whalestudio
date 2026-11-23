import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory Module
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem finite_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hb : Bornology.IsBounded S) : (S ∩ (L : Set E)).Finite := by
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  haveI : DiscreteTopology L.toAddSubgroup := ‹DiscreteTopology L›
  have hc : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  exact Metric.finite_isBounded_inter_isClosed ⟨(‹DiscreteTopology L› : DiscreteTopology L)⟩ hb hc

theorem fiber_count_le_ncard_inter_lattice (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (S : Set E) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (x : E) :
    ∑' g : L, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal) ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
  classical
  by_cases hx : ∃ g0 : L, x ∈ g0 +ᵥ ((2⁻¹ : ℝ) • S)
  swap
  · push_neg at hx
    simp [Set.indicator_of_notMem (hx _)]
  obtain ⟨g0, hg0⟩ := hx

  have key : ∀ g : L, x ∈ g +ᵥ ((2⁻¹ : ℝ) • S) → ((g : E) - g0) ∈ S := by
    intro g hg
    rw [Set.mem_vadd_set] at hg hg0
    obtain ⟨a, ha, hax⟩ := hg
    obtain ⟨c, hc, hcx⟩ := hg0
    rw [Set.mem_smul_set] at ha hc
    obtain ⟨s1, hs1, rfl⟩ := ha
    obtain ⟨s2, hs2, rfl⟩ := hc
    rw [Submodule.vadd_def, vadd_eq_add] at hax hcx
    have e : (g : E) - g0 = (2⁻¹ : ℝ) • s2 + (2⁻¹ : ℝ) • (-s1) := by
      rw [smul_neg, eq_sub_of_add_eq hax, eq_sub_of_add_eq hcx]; abel
    rw [e]
    exact hconv hs2 (hsymm s1 hs1) (by norm_num) (by norm_num) (by norm_num)
  have hfin : {g : L | ((g : E) - g0) ∈ S}.Finite := by
    have hinj : Function.Injective (fun g : L => (g : E) - g0) :=
      fun a b h => Subtype.ext (sub_left_injective h)
    refine ((finite_inter_lattice L S hb).preimage hinj.injOn).subset ?_
    intro g hg
    exact Set.mem_inter hg (sub_mem g.2 g0.2)
  rw [tsum_eq_sum (s := hfin.toFinset) (fun g hg => Set.indicator_of_notMem
    (fun h => hg (hfin.mem_toFinset.2 (key g h))) _)]
  calc ∑ g ∈ hfin.toFinset, ((g +ᵥ ((2⁻¹ : ℝ) • S)).indicator 1 x : ENNReal)
      ≤ ∑ g ∈ hfin.toFinset, (1 : ENNReal) := by
        refine Finset.sum_le_sum fun g _ => ?_
        unfold Set.indicator; split_ifs <;> simp
    _ = (hfin.toFinset.card : ENNReal) := by simp
    _ ≤ ((S ∩ (L : Set E)).ncard : ENNReal) := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        have hh := Set.ncard_le_ncard_of_injOn (s := {g : L | ((g : E) - g0) ∈ S})
          (t := S ∩ (L : Set E)) (fun g : L => (g : E) - g0)
          (fun g hg => Set.mem_inter hg (sub_mem g.2 g0.2))
          (fun a _ b _ h => Subtype.ext (sub_left_injective h)) (finite_inter_lattice L S hb)
        exact_mod_cast hh

theorem measure_div_le_ncard_inter_lattice (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (S : Set E)
    (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S) (hb : Bornology.IsBounded S)
    (hm : MeasurableSet S) :
    (μ S).toReal / (2 ^ finrank ℝ E * ZLattice.covolume L μ) ≤ ((S ∩ (L : Set E)).ncard : ℝ) := by
  classical
  haveI : MeasureTheory.VAddInvariantMeasure L E μ :=
    ⟨fun g s _ => by simp only [Submodule.vadd_def, vadd_eq_add]; exact measure_preimage_add μ (g : E) s⟩
  have hF : MeasureTheory.IsAddFundamentalDomain L
      (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) μ :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ hF
  have hpos : 0 < ZLattice.covolume L μ := ZLattice.covolume_pos L μ
  have hTm : MeasurableSet ((2⁻¹ : ℝ) • S) := hm.const_smul₀ _
  have hle : μ ((2⁻¹ : ℝ) • S) ≤ ((S ∩ (L : Set E)).ncard : ENNReal)
      * μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [hF.measure_eq_tsum ((2⁻¹ : ℝ) • S)]
    calc ∑' g : L, μ ((g +ᵥ (2⁻¹ : ℝ) • S)
          ∩ ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L))
        = ∑' g : L, ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ := by
          congr 1; funext g
          rw [lintegral_indicator_one (hTm.const_vadd g), Measure.restrict_apply (hTm.const_vadd g)]
      _ = ∫⁻ y in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ∑' g : L, ((g +ᵥ (2⁻¹ : ℝ) • S).indicator 1 y : ENNReal) ∂μ :=
          (lintegral_tsum fun g => (measurable_one.indicator (hTm.const_vadd g)).aemeasurable).symm
      _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L),
            ((S ∩ (L : Set E)).ncard : ENNReal) ∂μ :=
          lintegral_mono fun y => fiber_count_le_ncard_inter_lattice L S hconv hsymm hb y
      _ = _ := setLIntegral_const _ _
  have hFfin : μ (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) ≠ ⊤ := by
    intro h
    rw [hcov, Measure.real, h] at hpos
    simp at hpos
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hFfin) hle
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (by positivity), inv_pow, ENNReal.toReal_natCast] at hreal
  have h2 : (0 : ℝ) < 2 ^ finrank ℝ E := by positivity
  rw [inv_mul_le_iff₀ h2] at hreal
  rw [div_le_iff₀ (mul_pos h2 hpos), hcov, Measure.real]
  calc (μ S).toReal ≤ _ := hreal
    _ = _ := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
