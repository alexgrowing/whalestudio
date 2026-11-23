import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ContinuousAdelicGL2Det

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

instance instT2SpaceUnitaryPQ (P Q : ℕ) : T2Space (UpqT P Q) := (isClosedEmbedding_mat P Q).isEmbedding.t2Space

section SlopeTestRemainingChoices

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem continuousOn_cayInv : ContinuousOn (cayInv P Q) (cayS (D0 P Q)) := by
  have e : cayInv P Q = fun g => ⟨cayCand P Q g, cayCand_mem P Q g⟩ := by
    funext g
    first
    | (unfold cayInv; rw [dif_pos (cayCand_mem P Q g)])
    | simp [cayInv, cayCand_mem]
  rw [e]
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  show ContinuousOn (cayCand P Q) (cayS (D0 P Q))
  intro g hg
  have hg' : ∃ X ∈ D0 P Q, g.mat * (1 + 1 - (X : Mat)) = 1 + 1 + (X : Mat) := hg
  obtain ⟨X, -, hgX⟩ := hg'
  have h4 : (g.mat + 1) * (1 + 1 - (X : Mat)) = (4 : ℂ) • (1 : Mat) := by
    rw [add_mul, hgX, one_mul, show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul,
      one_smul]
    abel
  have hdet : IsUnit (g.mat + 1).det := by
    have h5 := congrArg Matrix.det h4
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h5
    have h' : IsUnit ((g.mat + 1).det * (1 + 1 - (X : Mat)).det) := by
      rw [h5]
      exact (Ne.isUnit (by norm_num : (4 : ℂ) ≠ 0)).pow _
    exact isUnit_of_mul_isUnit_left h'
  unfold cayCand
  have hc : ContinuousAt (fun g : UpqT P Q => g.mat) g := continuous_mat.continuousAt
  have hinv : ContinuousAt (fun g : UpqT P Q => (g.mat + 1)⁻¹) g := by
    refine (continuousAt_matrix_inv _ ?_).comp (hc.add continuousAt_const)
    obtain ⟨u, hu⟩ := hdet
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact ((continuousAt_const.mul hinv).mul (hc.sub continuousAt_const)).continuousWithinAt

theorem betaH_apply (lam : Measure (lieU P Q)) (S : Set (UpqT P Q)) (hS : MeasurableSet S) :
    betaH P Q lam S = ∫⁻ X in cayF P Q ⁻¹' S ∩ D0 P Q, rhoH P Q X ∂lam := by
  unfold betaH
  rw [Measure.map_apply measurable_cayF hS, withDensity_apply _ (measurable_cayF hS),
    Measure.restrict_restrict (measurable_cayF hS)]

theorem preimage_subset_image (S : Set (UpqT P Q)) :
    cayF P Q ⁻¹' S ∩ D0 P Q ⊆ cayInv P Q '' S := by
  rintro X ⟨hXS, hXD⟩
  exact ⟨cayF P Q X, hXS, cayInv_cayF X hXD⟩

end SlopeTestRemainingChoices

theorem cayleyDens_of (hH : HuaInv) (hL : LocalHaarUnique) (hE : ExpCay) : CayleyDens := by
  intro P Q m hm c hc0 hcT lam hlam hlim
  haveI := hlam.1
  haveI := hm
  set β := betaH P Q lam with hβdef
  set W := cayS (D0 P Q) with hWdef
  have hWo : IsOpen W := isOpen_cayley_domain
  have h1W : (1 : UpqT P Q) ∈ W := by
    refine ⟨0, zero_mem_cayley_domain, ?_⟩
    rw [mat_one, ZeroMemClass.coe_zero]
    simp

  have hfin : ∀ K, IsCompact K → K ⊆ W → β K ≠ ⊤ := by
    intro K hK hKW
    rw [hβdef, betaH_apply lam K hK.measurableSet]
    set C := cayInv P Q '' K
    have hC : IsCompact C := hK.image_of_continuousOn (continuousOn_cayInv.mono hKW)
    have hCD : C ⊆ D0 P Q := by
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨X, hX, h⟩ := hKW hg
      rw [cayley_inverse_iff P Q g X h]
      exact hX
    rcases C.eq_empty_or_nonempty with hCe | hCn
    · have : cayF P Q ⁻¹' K ∩ D0 P Q = ∅ := Set.subset_eq_empty (preimage_subset_image K) hCe
      rw [this, Measure.restrict_empty, lintegral_zero_measure]
      exact ENNReal.zero_ne_top
    obtain ⟨X0, hX0C, hmax⟩ := hC.exists_isMaxOn hCn
      (fun X hX => (continuousAt_rhoH X (hCD hX)).continuousWithinAt)
    have hbound : ∫⁻ X in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q X ∂lam ≤
        ∫⁻ _ in C, rhoH P Q X0 ∂lam := by
      calc ∫⁻ X in cayF P Q ⁻¹' K ∩ D0 P Q, rhoH P Q X ∂lam
          ≤ ∫⁻ X in C, rhoH P Q X ∂lam := lintegral_mono_set (preimage_subset_image K)
        _ ≤ ∫⁻ _ in C, rhoH P Q X0 ∂lam := setLIntegral_mono measurable_const (fun X hX => hmax hX)
    refine ne_top_of_le_ne_top ?_ hbound
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.measure_lt_top.ne

  have hne : β W ≠ 0 := by
    rw [hβdef, betaH_apply lam W hWo.measurableSet]
    have e : cayF P Q ⁻¹' W ∩ D0 P Q = D0 P Q := by
      refine Set.inter_eq_right.2 fun X hX => ?_
      exact ⟨X, hX, cayF_spec X hX⟩
    rw [e]
    intro h0
    rw [lintegral_eq_zero_iff measurable_rhoH,
      Filter.EventuallyEq, ae_restrict_iff' isOpen_cell_domain.measurableSet] at h0
    have hD : lam (D0 P Q) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [h0] with X hX hXD
      exact rhoH_pos X hXD (hX hXD)
    exact isOpen_cell_domain.measure_ne_zero lam ⟨0, zero_mem_cayley_domain⟩ hD
  obtain ⟨t, ht0, htT, W', hW'1, hW'W, hres⟩ :=
    hL (UpqT P Q) m hm β W hWo h1W (hH P Q lam hlam.1) hfin hne
  set W'' := interior W' with hW''def
  have hW''o : IsOpen W'' := isOpen_interior
  have h1W'' : (1 : UpqT P Q) ∈ W'' := mem_interior_iff_mem_nhds.2 hW'1
  have hW''W : W'' ⊆ W := interior_subset.trans hW'W
  have hres'' : β.restrict W'' = t • m.restrict W'' := by
    have e1 := congrArg (fun μ : Measure (UpqT P Q) => μ.restrict W'') hres
    simp only [Measure.restrict_restrict hW''o.measurableSet, Measure.restrict_smul] at e1
    rwa [Set.inter_eq_left.2 (interior_subset : W'' ⊆ W')] at e1
  set D : Set (lieU P Q) := D0 P Q ∩ cayF P Q ⁻¹' W'' with hDdef
  have hD0 : D ∈ 𝓝 (0 : lieU P Q) := by
    refine Filter.inter_mem (isOpen_cell_domain.mem_nhds zero_mem_cayley_domain) ?_
    apply (continuousOn_cayF.continuousAt (isOpen_cell_domain.mem_nhds zero_mem_cayley_domain)).preimage_mem_nhds
    rw [cayF_zero]
    exact hW''o.mem_nhds h1W''
  have hDm : MeasurableSet D := isOpen_cell_domain.measurableSet.inter (measurable_cayF hW''o.measurableSet)
  have hcayS : cayS D = W'' := by
    ext g
    constructor
    · rintro ⟨X, ⟨-, hXW⟩, h⟩
      rw [← cayF_eq_of g X h]
      exact hXW
    · intro hg
      obtain ⟨X, hX, h⟩ := hW''W hg
      have e := cayF_eq_of g X h
      exact ⟨X, ⟨hX, by rw [Set.mem_preimage, e]; exact hg⟩, h⟩
  have htinv : t⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ht0
  set f : lieU P Q → ℝ≥0∞ := fun X => t⁻¹ * rhoH P Q X with hfdef
  have hfm : Measurable f := measurable_rhoH.const_mul _
  have hfc : ContinuousAt f 0 :=
    (ENNReal.continuous_const_mul htinv).continuousAt.comp (continuousAt_rhoH 0 zero_mem_cayley_domain)
  have hf0 : f 0 ≠ ⊤ := ENNReal.mul_ne_top htinv ENNReal.ofReal_ne_top
  have hmap : (m.restrict (cayS D)).map (cayInv P Q) = (lam.restrict D).withDensity f := by
    rw [hcayS]
    have hm'' : m.restrict W'' = t⁻¹ • β.restrict W'' := by
      rw [hres'', smul_smul, ENNReal.inv_mul_cancel ht0 htT, one_smul]
    have hβmap : (β.restrict W'').map (cayInv P Q) = (lam.restrict D).withDensity (rhoH P Q) := by
      rw [hβdef]
      unfold betaH
      rw [Measure.restrict_map measurable_cayF hW''o.measurableSet,
        Measure.map_map (cayley_inverse_measurable P Q) measurable_cayF,
        restrict_withDensity (measurable_cayF hW''o.measurableSet), Measure.restrict_restrict
          (measurable_cayF hW''o.measurableSet), Set.inter_comm, ← hDdef]
      have hae : (cayInv P Q ∘ cayF P Q) =ᵐ[(lam.restrict D).withDensity (rhoH P Q)] id := by
        refine (withDensity_absolutelyContinuous _ _).ae_le ?_
        filter_upwards [ae_restrict_mem hDm] with X hX
        exact cayInv_cayF X hX.1
      rw [Measure.map_congr hae, Measure.map_id]
    rw [hm'', Measure.map_smul, hβmap]
    have ef : f = t⁻¹ • rhoH P Q := by
      funext X
      simp [hfdef]
    rw [ef, withDensity_smul _ measurable_rhoH]
  have hexp := hE P Q m lam hlam.1 D hD0 hDm f hfm hfc hf0 hmap
  have hc : f 0 = c := tendsto_nhds_unique hexp hlim
  refine ⟨D, hD0, hDm, f, hfm, ?_, hmap⟩
  rw [← hc]
  exact hfc

theorem cayleyLoc_of_parts (hH : HuaInv) (hL : LocalHaarUnique) (hE : ExpCay) : CayleyLoc := by
  exact cayleyLoc_of cayley_inverse_measurable cayley_inverse_iff cayley_set_measurable (cayleyDens_of hH hL hE)

end HcInf
