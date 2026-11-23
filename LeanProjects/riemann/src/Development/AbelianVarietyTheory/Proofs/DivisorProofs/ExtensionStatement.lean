import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComplementOpenDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothContinuousLimsupExtEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySmoothBoundPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperSemicontinuousLimsupExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialContinuousOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshOfLocallyIsPshStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOnStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

namespace GlobalTheory.ExtLogGrowth
open Filter Topology

open ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic in

theorem extension_of_log_growth : GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic.Extension := by
  intro D Y _ _ _ A L s m W hB Θ u C₁ hΘ hu hpos hgr
  obtain ⟨hop, hde⟩ := GlobalTheory.T.boundary_complement_open_dense D Y A L s m W hB
  obtain ⟨hcont, heq⟩ := GlobalTheory.T.smooth_continuous_limsup_ext_eq D Y A (opn s) u hop hu
  have hloc : ∀ y : Y, ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ ∃ M : ℝ, ∀ y' ∈ O ∩ opn s, u y' ≤ M := by
    intro y
    by_cases hy : y ∈ opn s
    · have hca : ContinuousAt u y := hcont.continuousAt (hop.mem_nhds hy)
      obtain ⟨O, hO, hOo, hyO⟩ :=
        mem_nhds_iff.1 (hca.preimage_mem_nhds (Iio_mem_nhds (lt_add_one (u y))))
      exact ⟨O, hOo, hyO, u y + 1, fun y' hy' => (hO hy'.1).le⟩
    · obtain ⟨j, hj⟩ := A.cover y
      have hz0 : A.chart j y ∈ chartPart A j (Θ.U y) :=
        ⟨(A.chart j).map_source hj, by
          show (A.chart j).symm (A.chart j y) ∈ Θ.U y
          rw [(A.chart j).left_inv hj]; exact Θ.mem_U y⟩
      obtain ⟨V, hVo, hz0V, ⟨M, hM⟩, -⟩ := GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr y j _ hz0
        (by rwa [(A.chart j).left_inv hj])
      refine ⟨(A.chart j).source ∩ A.chart j ⁻¹' V, (A.chart j).isOpen_inter_preimage hVo,
        ⟨hj, hz0V⟩, M, ?_⟩
      rintro y' ⟨⟨hy's, hy'V⟩, hy'o⟩
      have := hM _ hy'V (by rwa [(A.chart j).left_inv hy's])
      rwa [(A.chart j).left_inv hy's] at this
  choose O hOo hyO M hM using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hOo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hyO y⟩)
  have hbd : ∀ y ∈ opn s, u y ≤ ∑ y' ∈ t, |M y'| := by
    intro y hy
    obtain ⟨y', hy't, hyO'⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact (hM y' y ⟨hyO', hy⟩).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hy't))
  refine ⟨⟨_, hbd⟩, heq, ?_⟩
  intro x j
  have hvle : ∀ y, limsupExt (opn s) u y ≤ ((∑ y' ∈ t, |M y'| : ℝ) : EReal) := by
    intro y
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    exact eventually_nhdsWithin_of_forall fun y' hy' => EReal.coe_le_coe_iff.2 (hbd y' hy')
  have hUo : IsOpen (chartPart A j (Θ.U x)) :=
    (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)
  have hcompat : IsCompatChart A (A.chart j) := fun k => ⟨A.holo k j, A.holo j k⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z _
    exact (EReal.add_lt_top (EReal.coe_ne_top _) ((hvle _).trans_lt (EReal.coe_lt_top _)).ne).ne
  · intro z hz
    have hc : ContinuousWithinAt (fun z => ((2 * Θ.φ x ((A.chart j).symm z) : ℝ) : EReal))
        (chartPart A j (Θ.U x)) z :=
      continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
        ((continuousWithinAt_const.mul ((hΘ.1 x j).continuousOn z hz)))
    have hv : UpperSemicontinuousWithinAt (fun z => limsupExt (opn s) u ((A.chart j).symm z))
        (chartPart A j (Θ.U x)) z := by
      intro b hb
      have h1 := GlobalTheory.T.upperSemicontinuous_limsupExt Y (opn s) u ((A.chart j).symm z) b hb
      have h2 : Tendsto (A.chart j).symm (𝓝[chartPart A j (Θ.U x)] z) (𝓝 ((A.chart j).symm z)) :=
        ((A.chart j).continuousOn_symm z hz.1).mono_left (nhdsWithin_mono _ fun w hw => hw.1)
      exact h2.eventually h1
    refine hc.upperSemicontinuousWithinAt.add' hv ?_
    exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  · intro z hz
    rw [mem_closure_iff_nhds]
    intro T hT
    have hTU : T ∩ chartPart A j (Θ.U x) ∈ 𝓝 z := Filter.inter_mem hT (hUo.mem_nhds hz)
    have himg : (A.chart j).symm '' (T ∩ chartPart A j (Θ.U x)) ∈ 𝓝 ((A.chart j).symm z) :=
      (A.chart j).symm.image_mem_nhds hz.1 hTU
    obtain ⟨y, ⟨z', hz', rfl⟩, hyo⟩ := mem_closure_iff_nhds.1 (hde ((A.chart j).symm z)) _ himg
    refine ⟨z', hz'.1, hz'.2, ?_⟩
    show ((2 * Θ.φ x ((A.chart j).symm z') : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm z') ≠ ⊥
    rw [heq _ hyo, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  · intro κ
    apply GlobalTheory.T.isPsh_of_locally_isPsh D _ _ hUo
    intro z₀ hz₀
    by_cases hy : (A.chart j).symm z₀ ∈ opn s
    · obtain ⟨hVo, -, -, hVpsh⟩ := GlobalTheory.T.chart_potential_continuous_on D Y A Θ u (opn s) x (A.chart j) hop hΘ hu hpos hcompat
      refine ⟨_, hVo, ⟨hz₀.1, hz₀.2, hy⟩, GlobalTheory.T.isPsh_congr_divisor D _ _ _ (hVpsh κ) ?_⟩
      intro w hw
      show _ = (max (((2 * Θ.φ x ((A.chart j).symm w) : ℝ) : EReal) + limsupExt (opn s) u ((A.chart j).symm w)) ((-κ : ℝ) : EReal)).toReal
      rw [heq _ hw.2.2, ← EReal.coe_add, ← (EReal.coe_strictMono.monotone).map_max, EReal.toReal_coe]
    · obtain ⟨V, hVo, hz₀V, -, hV⟩ := GlobalTheory.T.boundary_smooth_bound_potential D Y A L s m W hB Θ u C₁ hΘ hu hpos hgr x j z₀ hz₀ hy
      exact ⟨V, hVo, hz₀V, hV κ⟩

end GlobalTheory.ExtLogGrowth
