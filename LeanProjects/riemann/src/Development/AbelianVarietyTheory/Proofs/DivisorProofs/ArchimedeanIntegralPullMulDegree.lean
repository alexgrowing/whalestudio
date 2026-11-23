import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open MeasureTheory GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchPull

open Set

theorem setIntegral_pull {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {e : ℕ} (hX : IsArithVar p e) (g : Y ⟶ X) (hY : IsArithVar (g ≫ p) e)
    (hη : g (genericPoint Y) = genericPoint X) (hδ : g.residueDegree (genericPoint Y) ≠ 0)
    (N : HermLB p) (σ : k →+* ℂ) (U : X.Opens) (hU : genericPoint X ∈ U)
    (f : CxPts p σ → ℝ) (hf : ContinuousOn f (ptsIn p σ U))
    (S' : Set (CxPts (g ≫ p) σ)) (hsub : ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ⊆ S')
    (f' : CxPts (g ≫ p) σ → ℝ)
    (hf' : EqOn f' (fun y => f (PtsOver.map g rfl _ y)) (ptsIn (g ≫ p) σ (g ⁻¹ᵁ U)))
    (ε : ℤˣ) :
    ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε =
      (g.residueDegree (genericPoint Y) : ℝ) * ∫ x in ptsIn p σ U, f x ∂(N.φ σ).chernPart e ε := by
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.CoverDeg.exists_open_covering_charts hX hY g rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  set F := PtsOver.map g (rfl : g ≫ p = g ≫ p) (spMap σ) with hFdef
  have hFm : Measurable F := (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : X.Opens, F ⁻¹' ptsIn p σ W = ptsIn (g ≫ p) σ (g ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn p σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn p σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : (N.φ σ).chernPart e ε (ptsIn p σ V)ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hX ((V : X.Opens) : Set X)ᶜ
      V.isOpen.isClosed_compl (by simp [hVη]) σ (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : (g.residueDegree (genericPoint Y) : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn p σ U) =
      Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict
        (F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V))) := by
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.CoverChern.chernPart_preimage_of_cover hX hY g rfl (N.φ σ) (N.cInf σ) ε (ptsIn p σ V)
        (isOpen_ptsIn V) _ hcard hchart hlift
        (fun c c' hc w hw => GlobalTheory.PullChartDens.chernDens_pull_of_chart g rfl (N.φ σ) (N.cInf σ)
          c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull h0]
  set T' := F ⁻¹' (ptsIn p σ U ∩ ptsIn p σ V) with hT'
  have hT'eq : T' = ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) ∩ ptsIn (g ≫ p) σ (g ⁻¹ᵁ V) := by
    rw [hT', Set.preimage_inter, hpre, hpre]
  have hT'm : MeasurableSet T' := hFm (hUm.inter hVm)
  have hT'U : T' ⊆ ptsIn (g ≫ p) σ (g ⁻¹ᵁ U) := by
    rw [hT'eq]; exact Set.inter_subset_left
  have h0' : ((N.φ σ).pull g rfl).chernPart e ε T'ᶜ = 0 := by
    have h := GlobalTheory.ChernNull.chernPart_over_closed hY (g ⁻¹' ((U ⊓ V : X.Opens) : Set X)ᶜ)
      ((U ⊓ V).isOpen.isClosed_compl.preimage g.continuous) (by simp [hη, hU, hVη]) σ
      ((N.φ σ).pull g rfl) ε
    convert h using 2
    rw [hT'eq]
    ext y
    simp [mem_ptsIn]

  have hae : S' =ᵐ[((N.φ σ).pull g rfl).chernPart e ε] T' := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => hx.2) h0', ?_⟩
    rw [Set.diff_eq_empty.2 (hT'U.trans hsub)]
    exact measure_empty
  have hfm : AEStronglyMeasurable f (Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T')) := by
    rw [← hmeas]
    exact (hf.aestronglyMeasurable hUm).smul_measure _
  calc ∫ y in S', f' y ∂((N.restr g).φ σ).chernPart e ε
      = ∫ y in T', f' y ∂((N.φ σ).pull g rfl).chernPart e ε := setIntegral_congr_set hae
    _ = ∫ y in T', f (F y) ∂((N.φ σ).pull g rfl).chernPart e ε :=
        setIntegral_congr_fun hT'm (hf'.mono hT'U)
    _ = ∫ x, f x ∂Measure.map F ((((N.φ σ).pull g rfl).chernPart e ε).restrict T') :=
        (integral_map hFm.aemeasurable hfm).symm
    _ = _ := by
        rw [← hmeas, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]

theorem archInt_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  intro k _ X Y _ _ p q e hX hY g hg hη hδ M N r hr
  subst hg
  have hη' : g (genericPoint Y) ⤳ genericPoint X := hη ▸ specializes_rfl
  have hU : genericPoint X ∈ (M.div hr).supp.compl := (M.div hr).genericPoint_notMem_supp
  have key : ∀ σ : k →+* ℂ,
      ((N.restr g).φ σ).chernInt e
        (offSupp (g ≫ p) σ ((M.restr g).div (MultPull.isRatSec_pull_map g hη' hr)))
        (logNorm ((M.restr g).φ σ) (fun c => Units.map (TrueGeo.SmallSec.fnMap g hη').toMonoidHom
          (r (c PUnit.unit)))) =
      (g.residueDegree (genericPoint Y) : ℝ) *
        (N.φ σ).chernInt e (offSupp p σ (M.div hr)) (logNorm (M.φ σ) r) := by
    intro σ
    have hsub := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.mem_offSupp_pull M g hη' hr hy
    have hf' := fun (y : CxPts (g ≫ p) σ) (hy : y ∈ ptsIn (g ≫ p) σ (g ⁻¹ᵁ (M.div hr).supp.compl)) =>
      ArchIntAlter.logNorm_pull M g hη' hr hy
    have hc := ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ)
    unfold Weight.chernInt
    rw [setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' 1,
      setIntegral_pull hX g hY hη hδ N σ _ hU _ hc _ hsub _ hf' (-1), mul_sub]
    rfl
  unfold HermLB.archInt
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.ArchPull
