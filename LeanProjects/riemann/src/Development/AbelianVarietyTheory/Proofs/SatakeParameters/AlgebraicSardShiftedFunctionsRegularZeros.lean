import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCotangentBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomeomorphZeroSet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEvalComplexPointLeSpanJacobianStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZeroStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false
noncomputable section
open TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.AlgSard

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {d : ℕ}

theorem countable_charts [SmoothOfRelativeDimension d p] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ C : Set (AlgChart p (RingHom.id ℂ) d), C.Countable ∧
      ∀ z ∈ ptsIn p (RingHom.id ℂ) U, ∃ ch ∈ C, z ∈ ch.e.source := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  obtain ⟨k, G, ⟨hom⟩⟩ := GlobalTheory.AffCxPts.homeomorph_zeroSet X p U hU hft
  haveI : SecondCountableTopology (ptsIn p (RingHom.id ℂ) U) := hom.secondCountableTopology
  choose ch hch using fun y : ptsIn p (RingHom.id ℂ) U =>
    AlgChart.exists_mem_source (p := p) (D := d) (σ := RingHom.id ℂ) y.1
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : ptsIn p (RingHom.id ℂ) U =>
      (Subtype.val ⁻¹' (ch y).e.source : Set (ptsIn p (RingHom.id ℂ) U)))
    (fun y => (ch y).e.open_source.preimage continuous_subtype_val)
  refine ⟨ch '' T, hT.image _, fun z hz => ?_⟩
  have hm : (⟨z, hz⟩ : ptsIn p (RingHom.id ℂ) U) ∈ ⋃ i ∈ T, Subtype.val ⁻¹' (ch i).e.source := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨z, hz⟩, hch _⟩
  obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 hm
  exact ⟨ch y, mem_image_of_mem _ hyT, hy⟩

end GlobalTheory.AlgSard

open GlobalTheory.AlgSard in

theorem GlobalTheory.AlgSard.main : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ φ : Fin d → Γ(X, U), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ c ∉ E, ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
        (∀ j, CxPts.evHom hz (φ j) + c j = 0) →
        RingHom.ker (CxPts.evHom hz) ≤
          Ideal.span (Set.range fun j => φ j + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (c j)) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU φ
  obtain ⟨C, hC, hcov⟩ := countable_charts (p := p) (d := d) hU
  choose E hE0 hE using fun ch : AlgChart p (RingHom.id ℂ) d => GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero X p d U ch φ
  refine ⟨⋃ ch ∈ C, E ch, (measure_biUnion_null_iff hC).2 fun ch _ => hE0 ch, ?_⟩
  intro c hc z hz hzero
  obtain ⟨ch, hchC, hzc⟩ := hcov z hz
  have hcz : c = fun j => -evHom hz (φ j) := funext fun j => by linear_combination hzero j
  have hdet : (ch.jacMat φ z).det ≠ 0 := fun h0 =>
    hc (mem_biUnion hchC (hcz ▸ hE ch z hzc hz h0))
  have key := GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian X p d U hU ch φ z hzc hz hdet
  have e : (fun j => φ j + algX p U (c j)) = fun j => φ j - algX p U (evHom hz (φ j)) := by
    funext j; rw [hcz, map_neg, sub_eq_add_neg]
  rw [e]; exact key
