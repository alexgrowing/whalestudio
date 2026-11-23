import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDivisorIntegralPushforwardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFiniteRestrictNearCodimOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrdPullbackMulResidueDegreeCodimOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicitiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem poincareLelong_sec : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro hP F _ X _ _ p σ e hX hdim L M s hs u hu
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hYi, π, hsm, hproj, hdimY, hgen, hdeg, hsnc⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p (e + 1) hX hdim (nonzeroLocus s).compl (fun h => h hs)
  haveI := hYi
  haveI : IsLocallyNoetherian Y := by
    haveI := SmoothOfRelativeDimension.smooth (e + 1) (π ≫ p)
    exact LocallyOfFiniteType.isLocallyNoetherian (π ≫ p)
  have hη : π (genericPoint Y) ⤳ genericPoint X := by rw [hgen]
  obtain ⟨s', hnz, hnsq, hmult⟩ := GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities F X Y p (π ≫ p) σ π rfl M s
  have hs' : genericPoint Y ∈ nonzeroLocus s' := by
    rw [hnz]; show π (genericPoint Y) ∈ nonzeroLocus s; rw [hgen]; exact hs
  have hsnc' : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s').compl) := by
    convert hsnc using 2
    ext x
    simp [hnz]
  have hPL := GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective F Y (π ≫ p) σ e hproj hsm (fun i => (L i).pull π rfl) (M.pull π rfl) s' hs' hsnc'
    (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)
  have hmu : Measurable u := (continuous_iff_continuousAt.2 fun y => (hu y).continuousAt).measurable
  have hml : Measurable (M.logSec s) := (GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ M s).1
  have hiso := GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F X Y p (π ≫ p) σ π rfl
  have hrefl := (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus F Y Y (π ≫ p) (π ≫ p) σ (𝟙 Y) (Category.id_comp _)).1
  have hdeg' : π.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have intEq : ∀ (A B : Fin (e + 1) → MLine (π ≫ p) σ), (∀ i, (A i).Isom (B i)) → ∀ f, Mix.int A f = Mix.int B f := by
    intro A B h f
    simp only [Mix.int, GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver F Y (π ≫ p) σ hproj (e + 1) A B h]
  have hlog : (M.pull π rfl).logSec s' = fun y => M.logSec s (ptMap π rfl σ y) := by
    funext y; simp only [MLine.logSec, hnsq]

  have hA : Mix.int (Fin.cons (MLine.ofFun (fun y => u (ptMap π rfl σ y)) (fun z => (hu _).pull π rfl)) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) ((M.pull π rfl).logSec s')
      = Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) := by
    rw [hlog, ← intEq (fun i => ((Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hml).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hiso.2.2.2.1 u hu
      · simpa using hrefl ((L j).pull π rfl)
  have hB : Mix.int (Fin.cons (M.pull π rfl) (fun i => (L i).pull π rfl) : Fin (e + 1) → MLine (π ≫ p) σ) (fun y => u (ptMap π rfl σ y))
      = Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
    rw [← intEq (fun i => ((Fin.cons M L : Fin (e + 1) → MLine p σ) i).pull π rfl)]
    · rw [(GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ (e + 1) hX hdim hproj π rfl hgen hdeg' _ _ hmu).2, hdeg]
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hrefl (M.pull π rfl)
      · simpa using hrefl ((L j).pull π rfl)
  have hS := GlobalTheory.T.finsum_divisorIntegral_pushforward F X Y p (π ≫ p) σ e hX hdim hproj hdimY π rfl hgen
    (divOfSec M.φ.isLB s hs) (divOfSec (M.pull π rfl).φ.isLB s' hs') (by
      intro z hz
      obtain ⟨i, hi⟩ := exists_chart M.φ.isLB z
      have hfin := GlobalTheory.T.exists_isFinite_restrict_near_codimOne F X Y p (π ≫ p) (e + 1) hX hdim hproj hdimY π rfl hgen z hz
      have hord := GlobalTheory.T.finsum_ord_pullback_mul_residueDegree_codim_one X Y π hη z hz hfin (ratOfSec s hs i : X.functionField) (Units.ne_zero _)
      calc _ = ∑ᶠ (w : Y) (_ : π w = z), Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w * (π.residueDegree w : ℤ) :=
            finsum_congr fun w => finsum_congr fun hw => by
              rw [hmult hη hs hs' w i (hw ▸ hi)]
        _ = _ := hord
        _ = _ := by
          rw [hdeg, Nat.cast_one, one_mul, ((presents_divOfRatSec M.φ.isLB _).isEqn i z hi).mult_eq])
    L u hmu
  rw [hA, hB, hS] at hPL
  exact hPL

end GlobalTheory
