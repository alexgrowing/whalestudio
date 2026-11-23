import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Metric Module Function
open scoped ENNReal

noncomputable section

theorem LatticePacking.card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ ρ) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * ρ + δ) / δ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hR : 0 < ρ + δ / 2 := by linarith
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : (⋃ c ∈ s, ball (c : E) (δ / 2)) ⊆ ball (0 : E) (ρ + δ / 2) := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs x hx]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1)
          = μ (⋃ c ∈ s, ball (c : E) (δ / 2)) := by
        rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ2]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (ρ + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hR]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ finrank ℝ E ≤ (ρ + δ / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hR.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ2.le _),
      ENNReal.toReal_natCast] at this
  have e : (2 * ρ + δ) / δ = (ρ + δ / 2) / (δ / 2) := by
    rw [div_eq_div_iff hδ.ne' hδ2.ne']; ring
  rw [e, div_pow, le_div_iff₀ (pow_pos hδ2 _)]
  exact K

theorem LatticePacking.proof : LatticePacking.Statement := by
  intro V _ _ L hL B hB hmin
  classical
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  let _ : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)
  have : IsAddTorsionFree V := .of_module_rat _
  have : Module.IsTorsionFree ℤ L :=
    Injective.moduleIsTorsionFree (R := ℤ) (fun y : L => (y : V)) Subtype.val_injective
      (fun _ _ => rfl)
  set δ : ℝ := Real.exp (-B) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by rw [hδdef, Real.exp_le_one_iff]; linarith
  let b := Module.Free.chooseBasis ℤ L
  let f : Module.Free.ChooseBasisIndex ℤ L → V := fun i => ((b i : L) : V)
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range f)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  have hdim : finrank ℝ W ≤ finrank ℤ L := by
    exact (finrank_range_le_card (R := ℝ) f).trans
      (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).ge
  have hW : ∀ x ∈ L, x ∈ W := by
    intro x hx
    have h1 : x = ∑ i, b.repr ⟨x, hx⟩ i • f i := by
      calc x = ((⟨x, hx⟩ : L) : V) := rfl
        _ = L.subtype (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, b.repr ⟨x, hx⟩ i • f i := by rw [map_sum]; rfl
    rw [h1]
    exact Submodule.sum_mem _ fun i _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  set S : Set V := {x : V | x ∈ L ∧ ‖x‖ ≤ 1} with hS
  set C : ℝ := ((2 * 1 + δ) / δ) ^ finrank ℝ W with hC
  have key : ∀ t : Finset V, (t : Set V) ⊆ S → (t.card : ℝ) ≤ C := by
    intro t ht
    have hcard : (t.subtype (· ∈ W)).card = t.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem]
      intro x hx
      exact hW x (ht hx).1
    rw [← hcard]
    refine LatticePacking.card_le_of_separated (t.subtype (· ∈ W)) hδ zero_le_one ?_ ?_
    · intro c hc
      rw [Finset.mem_subtype] at hc
      simpa using (ht hc).2
    · intro c hc d hd hcd
      rw [Finset.mem_subtype] at hc hd
      have hne : (c : V) - d ≠ 0 := sub_ne_zero.mpr fun h' => hcd (Subtype.ext h')
      have := hmin ((c : V) - d) (L.sub_mem (ht hc).1 (ht hd).1) hne
      simpa using this
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊C⌋₊ + 1)
    have h1 := key t ht
    rw [htc] at h1
    push_cast at h1
    have hC0 : 0 ≤ C := pow_nonneg (div_nonneg (by linarith) hδ.le) _
    linarith [Nat.lt_floor_add_one C]
  refine ⟨hfin, ?_⟩
  have h1 : (S.ncard : ℝ) ≤ C := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  refine h1.trans ?_
  have hq : (2 * 1 + δ) / δ ≤ 5 / δ := div_le_div_of_nonneg_right (by linarith) hδ.le
  have h5 : 1 ≤ 5 / δ := by rw [le_div_iff₀ hδ]; linarith
  have he : 5 / δ = Real.exp (B + Real.log 5) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), hδdef, Real.exp_neg, div_inv_eq_mul, mul_comm]
  calc C ≤ (5 / δ) ^ finrank ℝ W := pow_le_pow_left₀ (div_nonneg (by linarith) hδ.le) hq _
    _ ≤ (5 / δ) ^ finrank ℤ L := pow_le_pow_right₀ h5 hdim
    _ = Real.exp (finrank ℤ L * (B + Real.log 5)) := by rw [he, Real.exp_nat_mul]

end

end GroundTheory.Heights₂.Heights
