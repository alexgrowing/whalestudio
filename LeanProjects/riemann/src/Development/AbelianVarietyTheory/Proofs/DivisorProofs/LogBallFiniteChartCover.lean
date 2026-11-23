import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogMean

theorem exists_finite_chart_cover_logBallBd : ∀ {k : Type} [CommRing k] {Y : AlgebraicGeometry.Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ} [CompactSpace (GlobalTheory.CxPts p σ)] (f : GlobalTheory.CxPts p σ → ℝ), (∀ y₀, ∃ ch : GlobalTheory.AlgChart p σ d, y₀ ∈ ch.e.source ∧ GlobalTheory.LogMean.LogBallBd (f ∘ ch.e.symm) (ch.e y₀) (2 * d)) → ∃ (n : ℕ) (ch : Fin n → GlobalTheory.AlgChart p σ d) (K : Fin n → Set (ReciprocityTheory.L2DbarEstimates.V d)) (C ρ₀ : ℝ), 0 ≤ C ∧ 0 < ρ₀ ∧ (∀ j, IsCompact (K j) ∧ K j ⊆ (ch j).e.target) ∧ (∀ y, ∃ j, y ∈ (ch j).e.source ∧ (ch j).e y ∈ K j) ∧ ∀ j, ∀ v ∈ K j, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → MeasureTheory.IntegrableOn (f ∘ (ch j).e.symm) (Metric.ball v ρ) ∧ ∫ w in Metric.ball v ρ, f ((ch j).e.symm w) ≤ C * ρ ^ (2 * d) * (1 + Real.log (1 / ρ)) := by
  intro k _ Y p σ d _ f h
  have key : ∀ y₀, ∃ ch : GlobalTheory.AlgChart p σ d, ∃ δ C : ℝ, y₀ ∈ ch.e.source ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ C ∧
      Metric.closedBall (ch.e y₀) δ ⊆ ch.e.target ∧
      ∀ x ∈ Metric.closedBall (ch.e y₀) δ, ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ →
        MeasureTheory.IntegrableOn (f ∘ ch.e.symm) (Metric.ball x ρ) ∧
          ∫ w in Metric.ball x ρ, (f ∘ ch.e.symm) w ≤ C * ρ ^ (2 * d) * (1 + Real.log (1 / ρ)) := by
    intro y₀
    obtain ⟨ch, hy, hb⟩ := h y₀
    obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 ch.e.open_target (ch.e y₀) (ch.e.map_source hy)
    obtain ⟨δ, C, hδ, hδε, hC, hbd⟩ := hb.shrink (lt_min (half_pos hε) one_pos)
    refine ⟨ch, δ, C, hy, hδ, hδε.trans (min_le_right _ _), hC, ?_, hbd⟩
    exact (Metric.closedBall_subset_ball ((hδε.trans (min_le_left _ _)).trans_lt (half_lt_self hε))).trans hεs
  choose ch δ C hy hδ hδ1 hC hsub hbd using key
  let U : GlobalTheory.CxPts p σ → Set (GlobalTheory.CxPts p σ) := fun y =>
    (ch y).e.source ∩ (ch y).e ⁻¹' Metric.ball ((ch y).e y) (δ y)
  have hUo : ∀ y, IsOpen (U y) := fun y =>
    (ch y).e.continuousOn.isOpen_inter_preimage (ch y).e.open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y, by simp [hδ y]⟩)
  let eq := t.equivFin
  let idx : Fin t.card → GlobalTheory.CxPts p σ := fun j => (eq.symm j : GlobalTheory.CxPts p σ)
  have hidx : ∀ j, idx j ∈ t := fun j => (eq.symm j).2
  let ρ₀ : ℝ := (insert 1 (t.image δ)).min' (Finset.insert_nonempty _ _)
  let C₀ : ℝ := (insert 0 (t.image C)).max' (Finset.insert_nonempty _ _)
  have hρ₀1 : ρ₀ ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hρ₀δ : ∀ y ∈ t, ρ₀ ≤ δ y := fun y hyt =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hyt))
  have hρ₀ : 0 < ρ₀ := by
    rw [Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact one_pos
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ha
      exact hδ y
  have hC₀ : 0 ≤ C₀ := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hCC₀ : ∀ y ∈ t, C y ≤ C₀ := fun y hyt =>
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hyt))
  refine ⟨t.card, fun j => ch (idx j), fun j => Metric.closedBall ((ch (idx j)).e (idx j)) (δ (idx j)),
    C₀, ρ₀, hC₀, hρ₀, fun j => ⟨isCompact_closedBall _ _, hsub _⟩, ?_, ?_⟩
  · intro y
    have hy' := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy'
    obtain ⟨i, hi, hyU⟩ := hy'
    refine ⟨eq ⟨i, hi⟩, ?_⟩
    have he : idx (eq ⟨i, hi⟩) = i := by simp [idx]
    show y ∈ (ch (idx (eq ⟨i, hi⟩))).e.source ∧
      (ch (idx (eq ⟨i, hi⟩))).e y ∈ Metric.closedBall ((ch (idx (eq ⟨i, hi⟩))).e (idx (eq ⟨i, hi⟩))) (δ (idx (eq ⟨i, hi⟩)))
    rw [he]
    exact ⟨hyU.1, Metric.ball_subset_closedBall hyU.2⟩
  · intro j v hv ρ hρ hρρ₀
    obtain ⟨hint, hle⟩ := hbd (idx j) v hv ρ hρ (hρρ₀.trans (hρ₀δ _ (hidx j)))
    refine ⟨hint, hle.trans ?_⟩
    have hL : 0 ≤ 1 + Real.log (1 / ρ) := by
      have : 0 ≤ Real.log (1 / ρ) :=
        Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith [hρρ₀.trans hρ₀1])
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCC₀ _ (hidx j)) (pow_nonneg hρ.le _)) hL

end GlobalTheory.LogMean
