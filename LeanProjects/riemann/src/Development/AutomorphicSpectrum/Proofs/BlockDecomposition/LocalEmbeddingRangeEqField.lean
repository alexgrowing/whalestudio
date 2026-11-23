import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import GroundTheory.GlobalFields.LocalAtPlace
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.CompletionRange

theorem isClosed_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) : IsClosed (K.1 : Set (Om l)) := by
  haveI : FiniteDimensional ℚ_[l] K.1.toSubmodule := K.2
  exact Submodule.closed_of_finiteDimensional K.1.toSubmodule

theorem valued_le_one_of_norm_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hv
  have hv' : 1 < Valued.v x := not_le.1 hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv'
  have hy : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv'
  have ht : Filter.Tendsto (fun n : ℕ => x⁻¹ ^ n) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hy
  have ht' : Filter.Tendsto (fun n : ℕ => φ (x⁻¹ ^ n)) Filter.atTop (nhds 0) := by
    have h := (hφ.tendsto 0).comp ht
    rw [map_zero] at h
    exact h
  have hge : ∀ n : ℕ, 1 ≤ ‖φ (x⁻¹ ^ n)‖ := fun n => by
    have hφ0 : φ x ≠ 0 := (map_ne_zero φ).2 hx0
    rw [map_pow, map_inv₀, norm_pow, norm_inv]
    exact one_le_pow₀ ((one_le_inv₀ (norm_pos_iff.2 hφ0)).2 hx)
  have hn := ht'.norm
  rw [norm_zero] at hn
  have := ge_of_tendsto' hn hge
  linarith

theorem isClosed_image_integers {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    IsClosed (φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E))) := by
  have hc : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (w.adicCompletionIntegers E)))
  exact (hc.image hφ).isClosed

theorem range_eq_Kw : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  intro l _ E Ω _ _ _ _ Gw O _ _ _ Bw w φ hφ hE
  have hcl := isClosed_finExt Bw.Kw

  have key : ∀ k ∈ (Bw.Kw.1 : Set (Om l)), ‖k‖ ≤ 1 → k ∈ Set.range φ := by
    intro k hk hk1
    have hden : k ∈ closure (Set.range φ) := by
      refine closure_mono ?_ (Bw.j_dense hk)
      rintro _ ⟨y, rfl⟩
      exact ⟨algebraMap E _ y, hE y⟩
    have hS : IsOpen (Metric.closedBall (0 : Om l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hk' : k ∈ Metric.closedBall (0 : Om l) 1 := by simpa using hk1
    have h2 : k ∈ closure (Metric.closedBall (0 : Om l) 1 ∩ Set.range φ) :=
      hS.inter_closure ⟨hk', hden⟩
    have h3 : Metric.closedBall (0 : Om l) 1 ∩ Set.range φ ⊆
        φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
      rintro _ ⟨hb, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      exact valued_le_one_of_norm_le_one w φ hφ x (by simpa using hb)
    have h4 := closure_minimal h3 (isClosed_image_integers w φ hφ) h2
    obtain ⟨x, -, rfl⟩ := h4
    exact ⟨x, rfl⟩
  refine Set.Subset.antisymm ?_ fun k hk => ?_
  · rintro _ ⟨x, rfl⟩
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
      (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x (hcl.preimage hφ) fun y => ?_
    rw [hE y]
    exact Bw.j_E y
  · rcases le_total ‖k‖ 1 with h | h
    · exact key k hk h
    · have hinv : k⁻¹ ∈ (Bw.Kw.1 : Set (Om l)) := inv_mem hk
      obtain ⟨a, ha⟩ := key k⁻¹ hinv (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

end GlobalTheory.CompanionTheory.LTHodge.CompletionRange
