import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreCosinePushforwardUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleLineBundleChernRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackForm
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibCos

theorem map_eq_of_local {Z T : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [MeasurableSpace Z] (μ : Measure Z) (ν : Measure T) (f : Z → T) (hf : Measurable f) (v : Z → ℝ) (hv : Measurable v)
    (hloc : ∀ b₀ : T, ∃ U : Set T, IsOpen U ∧ b₀ ∈ U ∧ ∀ S : Set T, MeasurableSet S → S ⊆ U → ∀ J : Set ℝ,
      MeasurableSet J → μ (f ⁻¹' S ∩ v ⁻¹' J) = ν S * volume (J ∩ Set.Icc (0 : ℝ) 1)) :
    Measure.map v μ = ν Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  choose U hUo hU hUS using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun b _ => (hUo b).mem_nhds (hU b)
  ext J hJ
  have key : Measure.map f (μ.restrict (v ⁻¹' J)) = volume (J ∩ Set.Icc (0 : ℝ) 1) • ν := by
    refine Measure.ext_of_biUnion_eq_univ (S := (t : Set T)) t.countable_toSet
      (Set.eq_univ_of_univ_subset (by simpa using ht)) fun b _ => ?_
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.map_apply hf (hA.inter (hUo b).measurableSet),
      Measure.restrict_apply (hf (hA.inter (hUo b).measurableSet)),
      hUS b _ (hA.inter (hUo b).measurableSet) Set.inter_subset_right J hJ, Measure.smul_apply, smul_eq_mul, mul_comm]
  have e := congrArg (fun m : Measure T => m Set.univ) key
  simp only [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, smul_eq_mul] at e
  rw [Measure.map_apply hv hJ, e, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hJ, mul_comm]

end GlobalTheory.FibCos

theorem GlobalTheory.FibCos.map_part : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ,
      Measure.map v ((hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε) =
        (hB.atlas σ).part φ (-ε) Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε
  haveI : CompactSpace (CxPts q σ) := hB.compactSpace σ
  refine GlobalTheory.FibCos.map_eq_of_local _ _ _ (PtsOver.continuous_map π w (spMap σ)).measurable v
    (GlobalTheory.CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv) fun b₀ => ?_
  obtain ⟨U, hUo, hb, G, hG, hS⟩ := GlobalTheory.T.flag_bundle_line_bundle_chern_relation k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀
  refine ⟨U, hUo, hb, fun S hSm hSU J hJ => ?_⟩
  rw [hS S hSm hSU J hJ, setLIntegral_congr_fun hSm (fun b hb => GlobalTheory.T.fibre_cosine_pushforward_uniform (G b) (hG b (hSU hb)) J hJ),
    setLIntegral_const, mul_comm]
