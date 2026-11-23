import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FundPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ae_lact_notMem (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {Bad : Set (Frame X.Ψ r)} (hB : MeasurableSet Bad)
    (hinv : ∀ x, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ Bad ↔ x ∈ Bad))
    (h0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∀ᵐ z ∂muF X x0, lact γ (cpt X x0 z) ∉ Bad := by
  have hφ : Measurable (Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) :=
    measurable_one.indicator hB
  have hM := measInv_holds (E := E) r X x0 (lact γ x0) ho (KU.isOrth_lact X hγ ho)
    (Bad.indicator 1) hφ (fun x _ b hb => by
      classical
      simp only [Set.indicator_apply, hinv x b hb, Pi.one_apply])
  have h1 : ∫⁻ z, Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [h0] with z hz
    exact Set.indicator_of_notMem hz _
  rw [h1, KU.muF_lact X hγ] at hM
  have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (lact γ x0) z) :=
    hφ.comp (KU.cont_cpt X _).measurable
  have h2 := (lintegral_eq_zero_iff hm).1 hM.symm
  filter_upwards [h2] with z hz hbad
  rw [← KU.cpt_lact] at hbad
  simp only [Set.indicator_of_mem hbad, Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

theorem isFundSet_preimage (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ)
    (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ)
    (hp : X.p0 = r - j)
    (hfree : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1)
    (hnull : ∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 →
      muF X (x0F X) (proj X hj κ ⁻¹' N) = 0)
    (F : Set (Tau × Fin j × Fin (r - j) → ℂ)) (hF : IsFD (gammaU X hj κ) F) :
    ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧
      IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  obtain ⟨hFm, hFD, hcov, hbad⟩ := hF
  obtain ⟨N0, hN0, hN0m, hN0z⟩ := exists_measurable_superset_of_null hbad
  have ho := isOrth_x0F X
  have hOm : MeasurableSet (OmF X (x0F X)) :=
    ((FourierCoefficientDomain.isOpen_dom X).preimage (KU.cont_cpt X (x0F X))).measurableSet
  have hNm : MeasurableSet (F ∩ N0) := hFm.inter hN0m
  have hNz : muD Tau j (r - j) (F ∩ N0) = 0 := measure_mono_null Set.inter_subset_right hN0z
  refine ⟨F \ N0, hFm.diff hN0m, Set.sdiff_subset, ?_, ?_, Set.inter_subset_right, ?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]; exact hNz
  · exact (measurable_proj X hj κ (hFm.diff hN0m)).inter hOm
  · rintro z ⟨⟨hz, hzN⟩, hzO⟩ z' ⟨⟨hz', -⟩, -⟩ γ hγ b hb h
    have hd : domPt X hj κ (cpt X (x0F X) z') = domPt X hj κ (lact γ (cpt X (x0F X) z)) := by
      rw [h, KU.lact_rmul', domPt_rmul X hj κ hb]
    have hfix : domPt X hj κ (lact γ (cpt X (x0F X) z)) = domPt X hj κ (cpt X (x0F X) z) := by
      by_contra hne
      apply hzN
      apply hN0
      refine ⟨hz, toUpq X hj κ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
      · change flat (moebI _ (domPt X hj κ (cpt X (x0F X) z))) ∈ F
        rw [← domPt_lact X hj κ hp γ hzO, ← hd]
        exact hz'
      · change moebI _ (domPt X hj κ (cpt X (x0F X) z)) ≠ domPt X hj κ (cpt X (x0F X) z)
        rw [← domPt_lact X hj κ hp γ hzO]
        exact hne
    have h1 := hfree γ hγ _ hzO hfix
    rw [h1, KU.lact_one] at h
    have hS : cpt X (x0F X) z' ∈ KU.Sset X (x0F X) {z} := by
      rw [h, KU.rmul_mem_S X hb, KU.cpt_mem_S X ho]
      rfl
    exact ((KU.cpt_mem_S X ho z').1 hS).symm
  · have := KU.countable_Γ X
    have hA : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (fun x => flat (domPt X hj κ x)) ⁻¹' (F ∩ N0) := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (measurable_domPt X hj κ hNm) ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_preimage, domPt_rmul X hj κ hb]
      · exact measure_eq_zero_iff_ae_notMem.1
          (hnull _ hNm (Set.inter_subset_left.trans hFD) hNz)
    have hB : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (KU.Sset X (x0F X) (OmF X (x0F X)))ᶜ := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (KU.meas_S X ho hOm).compl ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_compl_iff, KU.rmul_mem_S X hb]
      · filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hz hn
        exact hn ((KU.cpt_mem_S X ho z).2 hz)
    filter_upwards [hA, hB, ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hzA hzB hzO
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγF⟩ := hcov _ (domPt_mem X hj κ hp hzO)
    rw [← domPt_lact X hj κ hp γ hzO] at hγF
    have h1 := hzA ⟨γ, hγ⟩
    obtain ⟨⟨z', b⟩, ⟨hz', hb⟩, he⟩ := not_not.1 (hzB ⟨γ, hγ⟩)
    have he' : rmul (cpt X (x0F X) z') b = lact γ (cpt X (x0F X) z) := he
    have hpr : proj X hj κ z' = flat (domPt X hj κ (lact γ (cpt X (x0F X) z))) := by
      rw [← he', domPt_rmul X hj κ hb]; rfl
    refine ⟨z', ⟨?_, hz'⟩, γ⁻¹, X.Γ.inv_mem hγ, b, hb, ?_⟩
    · rw [Set.mem_preimage, hpr]
      exact ⟨hγF, fun hn => h1 ⟨hγF, hn⟩⟩
    · rw [he', KU.lact_lact, inv_mul_cancel, KU.lact_one]

end GlobalTheory.FlagFibre.FundPre
