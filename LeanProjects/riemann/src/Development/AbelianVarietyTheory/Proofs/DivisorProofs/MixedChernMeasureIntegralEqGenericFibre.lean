import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormDensityChangeOfChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartDensBc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompact
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

open GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixGen

theorem ofReal_dens_trans {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) (c c' : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) :
    ENNReal.ofReal ((ε : ℤ) * dens L c y) =
      ENNReal.ofReal (‖transDet c.e c'.e y‖ ^ 2) * ENNReal.ofReal ((ε : ℤ) * dens L c' y) := by
  rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart k X p σ D L c c' y hy hy', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem map_part {k K : Type} [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] {X G : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) {D : ℕ} (hX : IsArithVar p D)
    (L : Fin D → MLine p (τ.comp (algebraMap k K))) (ε : ℤˣ) :
    Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε := by
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  obtain ⟨_, hT2, hSC⟩ := (IsArithVar.finite_emb_and_topology hX).2 (τ.comp (algebraMap k K))
  let h := hm.homeomorph (bcPt hp.w τ)
  haveI : T2Space (CxPts q τ) := h.isEmbedding.t2Space
  haveI : SecondCountableTopology (CxPts q τ) := h.isEmbedding.secondCountableTopology
  obtain ⟨hGi, _, _, _, hgen, _⟩ := GlobalTheory.Mix.genericFibre_facts k K X G p q j hp D hX
  obtain ⟨U, hU, hηU, t, ht⟩ := GenericCoords.exists_affine_etale_coords hX
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hηU
  have hTc : IsClosed {y : CxPts p (τ.comp (algebraMap k K)) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
    have e : {y : CxPts p (τ.comp (algebraMap k K)) | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} =
        (ptsIn p (τ.comp (algebraMap k K)) U)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [e]
    exact (isOpen_ptsIn _).isClosed_compl
  have hZG : IsClosed (j ⁻¹' (U : Set X)ᶜ) := hZ.preimage j.continuous
  have hgZG : genericPoint G ∉ j ⁻¹' (U : Set X)ᶜ := by
    simp only [Set.mem_preimage]
    rw [hgen]
    exact hgZ
  have key := GlueCoverNull.map_glueMeas_of_cover D (CxPts p (τ.comp (algebraMap k K))) (CxPts q τ)
    (AlgChart p (τ.comp (algebraMap k K)) D) (AlgChart q τ D) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).bc hp.w τ) c y))
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans L ε c c' y hy hy')
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans _ ε c c' y hy hy')
    (bcPt hp.w τ) hm.continuous _ hTc (fun c => ChernNull.chart_null hX hZ hgZ _ c)
    (fun c => ChernNull.chart_null_field K G q τ D _ hZG hgZG c) 1
    (fun x _ => by
      obtain ⟨w0, hw0⟩ := hm.surjective x
      exact Set.encard_eq_one.2 ⟨w0, Set.ext fun w =>
        ⟨fun hw => hm.injective (hw.trans hw0.symm), fun hw => hw ▸ hw0⟩⟩)
    (fun z hz => by
      have hmem : bcPt hp.w τ z ∈ ptsIn p (τ.comp (algebraMap k K)) U := by
        simpa [mem_ptsIn] using hz
      obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU t ht hmem
      obtain ⟨c', hz', hc'⟩ := GlobalTheory.Mix.exists_chart_dens_bc k K (algebraMap k K) X G p q j hp τ D c z hc
      exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2.1, by simp only [(hc' w hw).2.2 L]⟩⟩)
  rw [Nat.cast_one, one_smul] at key
  exact key

theorem part_int_generic : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  intro k K _ _ _ _ X G _ p q j hp τ D hX L
  have hmap := map_part hp τ hX L
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  have he : MeasurableEmbedding (bcPt hp.w τ) := (hm.homeomorph (bcPt hp.w τ)).measurableEmbedding
  refine ⟨hmap, fun f => ⟨?_, ?_⟩⟩
  · simp only [Intg]
    rw [← hmap 1, ← hmap (-1), he.integrable_map_iff, he.integrable_map_iff]
    rfl
  · simp only [Mix.int]
    rw [← hmap 1, ← hmap (-1), he.integral_map, he.integral_map]

end GlobalTheory.MixGen
