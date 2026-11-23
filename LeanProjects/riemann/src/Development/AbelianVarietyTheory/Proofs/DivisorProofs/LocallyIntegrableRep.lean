import Mathlib

open MeasureTheory

namespace GlobalTheory.LocRep

variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ}

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_zero (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) :
    ι 0 =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hlin 1 0 0] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_add (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v + w) =ᵐ[μ] fun x => ι v x + ι w x := by
  filter_upwards [hlin 1 v w] with x hx
  simpa using hx

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_smul (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (a : ℂ) (v : K) :
    ι (a • v) =ᵐ[μ] fun x => a * ι v x := by
  filter_upwards [hlin a v 0, _root_.GlobalTheory.LocRep.rep_zero hlin] with x hx h0
  simp only [add_zero] at hx
  rw [hx, h0, add_zero]

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sub (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (v w : K) :
    ι (v - w) =ᵐ[μ] fun x => ι v x - ι w x := by
  filter_upwards [hlin (-1) w v] with x hx
  rw [show v - w = (-1 : ℂ) • w + v by rw [neg_one_smul]; abel, hx]
  ring

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.rep_sum (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {J : Type} (s : Finset J)
    (v : J → K) : ι (∑ j ∈ s, v j) =ᵐ[μ] fun x => ∑ j ∈ s, ι (v j) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using _root_.GlobalTheory.LocRep.rep_zero hlin
  · intro j s hj ih
    filter_upwards [_root_.GlobalTheory.LocRep.rep_add hlin (v j) (∑ i ∈ s, v i), ih] with x h1 h2
    rw [Finset.sum_insert hj, h1, h2, Finset.sum_insert hj]

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in

theorem _root_.GlobalTheory.LocRep.exists_pairing
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) {C : Set G} (hC : IsCompact C) :
    ∃ Λ : K →L[ℂ] ℂ, ∀ v, Λ v = ∫ x in C, ι v x ∂μ := by
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : ∀ (a : ℂ) v w, ∫ x in C, ι (a • v + w) x ∂μ =
      a * ∫ x in C, ι v x ∂μ + ∫ x in C, ι w x ∂μ := by
    intro a v w
    rw [integral_congr_ae (ae_restrict_of_ae (hlin a v w)),
      integral_add ((hM v).1.const_mul a) (hM w).1, integral_const_mul]
  have hz : ∫ x in C, ι 0 x ∂μ = 0 := by
    rw [integral_congr_ae (ae_restrict_of_ae (_root_.GlobalTheory.LocRep.rep_zero hlin))]
    simp
  let L : K →ₗ[ℂ] ℂ :=
    { toFun := fun v => ∫ x in C, ι v x ∂μ
      map_add' := fun v w => by simpa using hint 1 v w
      map_smul' := fun a v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        simpa [hz] using hint a v 0 }
  refine ⟨L.mkContinuous M fun v => ?_, fun v => rfl⟩
  exact (norm_integral_le_integral_norm _).trans (hM v).2

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in
theorem _root_.GlobalTheory.LocRep.locallyIntegrable_rep [LocallyCompactSpace G]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) (v : K) :
    LocallyIntegrable (ι v) μ := by
  intro x
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := hloc C hC
  exact ⟨C, hCx, (hM v).1⟩

open MeasureTheory in
variable {G : Type} [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {ι : K → G → ℂ} in

theorem _root_.GlobalTheory.LocRep.rep_of_pairing [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [BorelSpace G]
    [IsLocallyFiniteMeasure μ]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    {v : K} {φ : G → ℂ} (hφ : LocallyIntegrable φ μ)
    (h : ∀ C, IsCompact C → ∫ x in C, ι v x ∂μ = ∫ x in C, φ x ∂μ) : ι v =ᵐ[μ] φ := by
  have hv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  have hdiff : (ι v - φ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' (hv.sub hφ) fun C hC => ?_
    simp only [Pi.sub_apply]
    rw [integral_sub (hv.integrableOn_isCompact hC) (hφ.integrableOn_isCompact hC), h C hC, sub_self]
  filter_upwards [hdiff] with x hx
  simpa [sub_eq_zero] using hx

end GlobalTheory.LocRep
