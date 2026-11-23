import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasStrictFDerivAtExpTwoUpperRightBlockElementP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdjointApplyMatrixUpperRightBlockElementP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLog
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapWithDensityOfJacobianComplexMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralHaarEqCompactSubgroupTransversal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem isUnit_mat (g : UpqT p q) : IsUnit (UpqT.mat g) := Units.isUnit _

theorem isCompact_Kc : IsCompact (Kc p q) := by
  have h : Kc p q = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : UpqT p q | UpqT.mat x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  have hcl : IsClosed (Kc p q) := by
    rw [h]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
    exact isClosed_eq (GlobalTheory.UpqTopology.continuous_mat.matrix_elem a b) continuous_const
  have hc : IsCompact (Set.univ.pi fun _ : Ix p q => Set.univ.pi fun _ : Ix p q => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine (GlobalTheory.UpqTopology.isClosedEmbedding_mat.isCompact_preimage (K := _) hc).of_isClosed_subset hcl ?_
  intro x hx a _ b _
  simpa using entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hx)) a b

theorem exists_action (L : Mat p q → (Fin p → Fin q → ℂ)) (hL : ContinuousOn L {g | IsUnit g})
    (hLk : ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B)
    (g : UpqT p q) : ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧
      ∀ B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  let ψ : UpqT p q → (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ) := fun g B => L (UpqT.mat (eP B * g))
  have key : ∀ (x κ : UpqT p q) (B' : Fin p → Fin q → ℂ), κ ∈ Kc p q → x = κ * eP B' →
      L (UpqT.mat x) = B' := by
    intro x κ B' hκ hx
    rw [hx, mat_mul, mat_eP]
    exact hLk _ _ (star_mul_of_mem_Kc hκ)
  have dec : ∀ g B, ∃ κ ∈ Kc p q, eP B * g = κ * eP (ψ g B) := by
    intro g B
    obtain ⟨κ, hκ, B', h⟩ := exists_cartan (eP B * g)
    have : ψ g B = B' := key _ κ B' hκ h
    exact ⟨κ, hκ, by rw [this]; exact h⟩
  have inv : ∀ g B, ψ g⁻¹ (ψ g B) = B := by
    intro g B
    obtain ⟨κ, hκ, h⟩ := dec g B
    refine key _ κ⁻¹ B ((Ksg p q).inv_mem hκ) ?_
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h, mul_inv_cancel_right]
  refine ⟨ψ g, ?_, ?_, dec g⟩
  · exact hL.comp_continuous
      (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_eP.mul continuous_const)) fun B => isUnit_mat _
  · refine Function.bijective_iff_has_inverse.2 ⟨ψ g⁻¹, inv g, fun B => ?_⟩
    have := inv g⁻¹ B
    rwa [inv_inv] at this

theorem haar_polar : ∀ (p q : ℕ) (m : Measure (UpqT p q)), m.IsHaarMeasure → ∃ (c : ℝ) (mK : Measure (UpqT p q)), 0 < c ∧ IsProbabilityMeasure mK ∧ mK (Kc p q)ᶜ = 0 ∧ (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) ∧ ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c * ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)) := by
  intro p q m hm
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure p q m hm
  haveI := isInvInvariant_of_right m
  obtain ⟨mK, hprob, hK0, hleft, hright⟩ :=
    GlobalTheory.exists_biinvariant_probability_on_compact_subgroup (UpqT p q) (Ksg p q) isCompact_Kc
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.PolarLogCont.exists_continuousOn_polar_log p q
  have hpos : ∀ B : Fin p → Fin q → ℂ, 0 < polJ (pY B) := fun B => one_pos.trans_le (one_le_polJ _)
  have hJc : Continuous fun B : Fin p → Fin q → ℂ => polJ (pY B) := (continuous_polJ p q).comp continuous_pY
  have hJm : Measurable fun B : Fin p → Fin q → ℂ => ENNReal.ofReal (polJ (pY B)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hdet : ∀ B : Fin p → Fin q → ℂ, LinearMap.det (sP (pY B)) = polJ (pY B) :=
    fun B => det_sinhc_eq_polarJacobian p q _ (SinhcPres.sAd_pY p q B)
  have hem : Measurable (eP : (Fin p → Fin q → ℂ) → UpqT p q) := continuous_eP.measurable
  haveI : IsLocallyFiniteMeasure
      ((volume : Measure (Fin p → Fin q → ℂ)).withDensity fun B => ENNReal.ofReal (polJ (pY B))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hJc
  obtain ⟨c, hc, hf⟩ := GlobalTheory.Twist.lintegral_haar_eq_transversal (UpqT p q) (Fin p → Fin q → ℂ) m mK
    (volume.withDensity fun B => ENNReal.ofReal (polJ (pY B))) (Kc p q) eP hem hK0 hright
    (by
      intro h0
      rw [withDensity_eq_zero_iff hJm.aemeasurable] at h0
      haveI : (volume : Measure (Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Fin p → Fin q → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (ae (volume : Measure (Fin p → Fin q → ℂ))).NeBot :=
        ae_neBot.2 fun h => (isOpen_univ.measure_ne_zero (volume : Measure (Fin p → Fin q → ℂ))
          Set.univ_nonempty) (by rw [h]; rfl)
      obtain ⟨B, hB⟩ := h0.exists
      exact absurd hB (by simpa using hpos B))
    (by
      intro C hC
      have hcomp : IsCompact (L '' (UpqT.mat '' C)) :=
        (hC.image GlobalTheory.UpqTopology.continuous_mat).image_of_continuousOn (hLc.mono (by
          rintro _ ⟨x, -, rfl⟩; exact isUnit_mat x))
      refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
      rintro B ⟨k, hk, hB⟩
      refine ⟨_, ⟨_, hB, rfl⟩, ?_⟩
      rw [mat_mul, mat_eP]
      exact hL _ B (star_mul_of_mem_Kc hk))
    (by
      intro g
      obtain ⟨ψ, hψc, hψb, hψ⟩ := exists_action L hLc hL g
      refine ⟨ψ, hψc.measurable, GlobalTheory.map_withDensity_of_jacobian p q _ ψ hJc hψc hψb ?_, hψ⟩
      have := jacobian_action_p p q (UpqT.mat g) ψ hψc (fun B => by
          obtain ⟨κ, hκ, h⟩ := hψ B
          obtain ⟨U, hU, V, hV, hm⟩ := (mem_Kc_iff κ).1 hκ
          refine ⟨U, hU, V, hV, ?_⟩
          have := congrArg UpqT.mat h
          rwa [mat_mul, mat_mul, mat_eP, mat_eP, hm] at this)
        (fun B => by rw [hdet]; exact hpos B) (SinhcPres.sAd_pY p q)
        (fun B => hasStrictFDerivAt_exp_two_pY p q B (hasDerivAt_exp_two_add_smul p q (pY B)))
      simpa only [hdet] using this)
  refine ⟨c, mK, hc, hprob, hK0, hleft, fun f hfm => ?_⟩
  rw [hf f hfm, lintegral_withDensity_eq_lintegral_mul _ hJm]
  · congr 1
    refine lintegral_congr fun B => ?_
    simp only [Pi.mul_apply, mul_comm]
  · exact Measurable.lintegral_prod_right' (f := fun z : (Fin p → Fin q → ℂ) × UpqT p q => f (z.2 * eP z.1))
      (hfm.comp (measurable_snd.mul (hem.comp measurable_fst)))

end GlobalTheory.CartanInt
