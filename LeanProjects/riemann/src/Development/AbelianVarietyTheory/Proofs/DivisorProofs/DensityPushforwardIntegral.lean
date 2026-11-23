import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureLeOfLocalLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityNullOffChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDensityNullOffChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegralDensityFormulaStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
namespace GlobalTheory.ArchLim

theorem densInt_pull_eq_of_cells : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral B] [IsIntegral Y], IsArithVar q n → IsArithVar p D → π (genericPoint Y) = genericPoint B → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ) (f : CxPts q σ → ℝ), IsDens ρ → IsDens g → Measurable f → IntegrableDens ρ (fun y => f (PtsOver.map π w (spMap σ) y)) → (∀ (c₀ : AlgChart q σ n), ∀ y ∈ c₀.e.source, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), y ∈ c.e.source ∧ IsCell ε π w c c' ∧ ∀ u ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε u x)) = g c (c.e.symm u)) → densInt ρ (fun y => f (PtsOver.map π w (spMap σ) y)) = densInt g f := by
  intro k _ B Y q p π w n r D ε σ _ _ hq hp hgen ρ g f hρ hg hf hint hcov
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp.isProjOver
  set Φ := PtsOver.map π w (spMap σ) with hΦ
  have hΦm : Measurable Φ := (PtsOver.continuous_map π w (spMap σ)).measurable
  set W : Set (CxPts q σ) := {u | ∃ c : AlgChart q σ n, u ∈ c.e.source} with hWdef
  have hWc : Wᶜ = {u | ∀ c : AlgChart q σ n, u ∉ c.e.source} := by ext u; simp [W]
  have hWo : IsOpen W := by
    have : W = ⋃ c : AlgChart q σ n, c.e.source := by ext u; simp [W]
    rw [this]; exact isOpen_iUnion fun c => c.e.open_source
  have hWcm : MeasurableSet Wᶜ := hWo.measurableSet.compl
  have hcell : ∀ u ∈ W, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), u ∈ c.e.source ∧ IsCell ε π w c c' ∧
      ∀ z ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε z x)) = g c (c.e.symm z) :=
    fun u hu => hcov hu.choose u hu.choose_spec
  let S : CxPts q σ → Set (CxPts q σ) := fun u => if h : u ∈ W then (hcell u h).choose.e.source else Set.univ
  have hSo : ∀ u, IsOpen (S u) := by
    intro u
    by_cases h : u ∈ W
    · simp only [S, dif_pos h]; exact (hcell u h).choose.e.open_source
    · simp only [S, dif_neg h]; exact isOpen_univ
  have hSm : ∀ u ∈ W, u ∈ S u := by
    intro u h
    simp only [S, dif_pos h]
    exact (hcell u h).choose_spec.choose_spec.1
  have hSc : ∀ u ∈ W, ∃ (c : AlgChart q σ n) (c' : AlgChart p σ D), S u = c.e.source ∧ IsCell ε π w c c' ∧
      ∀ z ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε z x)) = g c (c.e.symm z) := by
    intro u h
    obtain ⟨c', -, h2, h3⟩ := (hcell u h).choose_spec
    exact ⟨_, c', by simp only [S, dif_pos h], h2, h3⟩
  have hρ' : IsDens fun c y => -ρ c y := (GlobalTheory.MixDens.isDens_zero.sub hρ).congr fun c y _ => by simp
  have hg' : IsDens fun c y => -g c y := (GlobalTheory.MixDens.isDens_zero.sub hg).congr fun c y _ => by simp
  have nνP : part g Wᶜ = 0 := by rw [hWc]; exact GlobalTheory.T.density_null_off_charts k B q σ n g
  have nνM : part (fun c y => -g c y) Wᶜ = 0 := by rw [hWc]; exact GlobalTheory.T.density_null_off_charts k B q σ n _
  have nμP : part ρ (Φ ⁻¹' Wᶜ) = 0 := by rw [hWc]; exact GlobalTheory.T.fibre_density_null_off_charts k B Y q p π w n D σ hq hp hgen ρ
  have nμM : part (fun c y => -ρ c y) (Φ ⁻¹' Wᶜ) = 0 := by rw [hWc]; exact GlobalTheory.T.fibre_density_null_off_charts k B Y q p π w n D σ hq hp hgen _
  set fp : CxPts q σ → ℝ≥0∞ := fun u => ENNReal.ofReal (f u) with hfp
  set fm : CxPts q σ → ℝ≥0∞ := fun u => ENNReal.ofReal (-f u) with hfm
  set fa : CxPts q σ → ℝ≥0∞ := fun u => ENNReal.ofReal |f u| with hfa
  have hfpm : Measurable fp := hf.ennreal_ofReal
  have hfmm : Measurable fm := hf.neg.ennreal_ofReal
  have hfam : Measurable fa := hf.abs.ennreal_ofReal
  let Mp : Measure (CxPts p σ) → (CxPts q σ → ℝ≥0∞) → Measure (CxPts q σ) := fun μ h => (μ.withDensity (h ∘ Φ)).map Φ
  have Mp_apply : ∀ μ h A, MeasurableSet A → Mp μ h A = ∫⁻ y in Φ ⁻¹' A, h (Φ y) ∂μ := by
    intro μ h A hA
    simp only [Mp]
    rw [Measure.map_apply hΦm hA, withDensity_apply _ (hΦm hA)]
    rfl
  have Mp_null : ∀ (μ : Measure (CxPts p σ)) h, μ (Φ ⁻¹' Wᶜ) = 0 → Mp μ h Wᶜ = 0 := by
    intro μ h h0
    rw [Mp_apply μ h _ hWcm]
    exact setLIntegral_measure_zero _ _ h0
  have wd_null : ∀ (ν : Measure (CxPts q σ)) h, ν Wᶜ = 0 → ν.withDensity h Wᶜ = 0 := by
    intro ν h h0
    rw [withDensity_apply _ hWcm]
    exact setLIntegral_measure_zero _ _ h0
  set μP := part ρ
  set μM := part fun c y => -ρ c y
  set νP := part g
  set νM := part fun c y => -g c y
  have iP : ∫⁻ y, fa (Φ y) ∂μP ≠ ⊤ := by
    have h := hint.1.hasFiniteIntegral
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] at h
    exact h.ne
  have iM : ∫⁻ y, fa (Φ y) ∂μM ≠ ⊤ := by
    have h := hint.2.hasFiniteIntegral
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] at h
    exact h.ne
  have cell : ∀ u ∈ W, ∀ A, MeasurableSet A → A ⊆ S u →
      (Mp μP fp A + Mp μM fm A + (νM.withDensity fp A + νP.withDensity fm A) =
        Mp μM fp A + Mp μP fm A + (νP.withDensity fp A + νM.withDensity fm A)) ∧
      νP.withDensity fa A + νM.withDensity fa A ≤ Mp μP fa A + Mp μM fa A := by
    intro u hu A hA hAS
    obtain ⟨c, c', hSu, hc, hfib⟩ := hSc u hu
    rw [hSu] at hAS
    have jP := ne_top_of_le_ne_top iP (setLIntegral_le_lintegral (Φ ⁻¹' A) fun y => fa (Φ y))
    have jM := ne_top_of_le_ne_top iM (setLIntegral_le_lintegral (Φ ⁻¹' A) fun y => fa (Φ y))
    obtain ⟨e1, e2⟩ := GlobalTheory.T.fibre_integral_density_formula k B Y q p π w n r D ε σ c c' hq hp hc ρ g f hρ hg hf hfib A hA hAS jP jM
    simp only [Mp_apply _ _ A hA, withDensity_apply _ hA]
    exact ⟨e1, e2⟩
  have hN : νP.withDensity fa + νM.withDensity fa ≤ Mp μP fa + Mp μM fa :=
    GlobalTheory.T.measure_le_of_local_le _ _ _ S W hSo hSm (by
      rw [Measure.add_apply, wd_null _ _ nνP, wd_null _ _ nνM, add_zero])
      fun u hu A hA hAS => by rw [Measure.add_apply, Measure.add_apply]; exact (cell u hu A hA hAS).2
  have hnull₁ : (Mp μP fp + Mp μM fm + (νM.withDensity fp + νP.withDensity fm)) Wᶜ = 0 := by
    simp only [Measure.add_apply, Mp_null _ _ nμP, Mp_null _ _ nμM, wd_null _ _ nνP, wd_null _ _ nνM, add_zero]
  have hnull₂ : (Mp μM fp + Mp μP fm + (νP.withDensity fp + νM.withDensity fm)) Wᶜ = 0 := by
    simp only [Measure.add_apply, Mp_null _ _ nμP, Mp_null _ _ nμM, wd_null _ _ nνP, wd_null _ _ nνM, add_zero]
  have hM₁ := GlobalTheory.T.measure_le_of_local_le _ _ (Mp μM fp + Mp μP fm + (νP.withDensity fp + νM.withDensity fm)) S W hSo hSm hnull₁ fun u hu A hA hAS => by
    simp only [Measure.add_apply]; exact (cell u hu A hA hAS).1.le
  have hM₂ := GlobalTheory.T.measure_le_of_local_le _ _ (Mp μP fp + Mp μM fm + (νM.withDensity fp + νP.withDensity fm)) S W hSo hSm hnull₂ fun u hu A hA hAS => by
    simp only [Measure.add_apply]; exact (cell u hu A hA hAS).1.ge
  have hu := congrArg (fun μ : Measure (CxPts q σ) => μ Set.univ) (le_antisymm hM₁ hM₂)
  have hNu := Measure.le_iff'.1 hN Set.univ
  simp only [Measure.add_apply, Mp_apply _ _ _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_univ] at hu hNu
  have pa : ∀ u, fp u ≤ fa u := fun u => ENNReal.ofReal_le_ofReal (le_abs_self _)
  have ma : ∀ u, fm u ≤ fa u := fun u => ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have kP : ∫⁻ u, fa u ∂νP ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨iP, iM⟩) (le_self_add.trans hNu)
  have kM : ∫⁻ u, fa u ∂νM ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨iP, iM⟩) (le_add_self.trans hNu)
  have intP : Integrable f νP := ⟨hf.aestronglyMeasurable, by
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]; exact kP.lt_top⟩
  have intM : Integrable f νM := ⟨hf.aestronglyMeasurable, by
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]; exact kM.lt_top⟩
  have a1 : ∫⁻ y, fp (Φ y) ∂μP ≠ ⊤ := ne_top_of_le_ne_top iP (lintegral_mono fun y => pa _)
  have a2 : ∫⁻ y, fm (Φ y) ∂μM ≠ ⊤ := ne_top_of_le_ne_top iM (lintegral_mono fun y => ma _)
  have a3 : ∫⁻ u, fp u ∂νM ≠ ⊤ := ne_top_of_le_ne_top kM (lintegral_mono fun y => pa _)
  have a4 : ∫⁻ u, fm u ∂νP ≠ ⊤ := ne_top_of_le_ne_top kP (lintegral_mono fun y => ma _)
  have a5 : ∫⁻ y, fp (Φ y) ∂μM ≠ ⊤ := ne_top_of_le_ne_top iM (lintegral_mono fun y => pa _)
  have a6 : ∫⁻ y, fm (Φ y) ∂μP ≠ ⊤ := ne_top_of_le_ne_top iP (lintegral_mono fun y => ma _)
  have a7 : ∫⁻ u, fp u ∂νP ≠ ⊤ := ne_top_of_le_ne_top kP (lintegral_mono fun y => pa _)
  have a8 : ∫⁻ u, fm u ∂νM ≠ ⊤ := ne_top_of_le_ne_top kM (lintegral_mono fun y => ma _)
  have ht := congrArg ENNReal.toReal hu
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨a1, a2⟩) (ENNReal.add_ne_top.2 ⟨a3, a4⟩),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨a5, a6⟩) (ENNReal.add_ne_top.2 ⟨a7, a8⟩),
    ENNReal.toReal_add a1 a2, ENNReal.toReal_add a3 a4, ENNReal.toReal_add a5 a6, ENNReal.toReal_add a7 a8] at ht
  simp only [densInt]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint.1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint.2,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part intP,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part intM]
  simp only [hfp, hfm] at ht
  linarith

end GlobalTheory.ArchLim
