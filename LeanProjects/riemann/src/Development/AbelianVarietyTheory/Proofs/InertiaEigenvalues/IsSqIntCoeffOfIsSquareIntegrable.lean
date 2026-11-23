import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL MeasureTheory

namespace GlobalTheory.LocGL.SqIntBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V}

theorem exists_central_scalar (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) {z : GL (Fin N) k}
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
  obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]⟩
  have hc' : ∀ v, π z v = c • v := hc
  refine ⟨c, ?_, hc'⟩
  obtain ⟨B, -, hp, hB⟩ := hu
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  have h1 := congrArg norm (hB z v v)
  rw [hc'] at h1
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, norm_mul, RingHom.id_apply, RCLike.norm_conj] at h1
  have h2 : 0 < ‖B v v‖ := norm_pos_iff.2 h0
  have h3 : ‖c‖ * ‖c‖ = 1 := mul_right_cancel₀ h2.ne' (by rw [mul_assoc, h1, one_mul])
  nlinarith [norm_nonneg c]

theorem norm_coeff_out (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π) (v : V) (l : Module.Dual ℂ V)
    (g : GL (Fin N) k) : ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
  obtain ⟨c, h1, hc⟩ := exists_central_scalar hs hi hu z.2
  rw [hz, map_mul, Module.End.mul_apply, hc, map_smul, map_smul, norm_smul, h1, one_mul]

omit [ValuativeRel k] in

theorem isLocallyConstant_orbit [IsTopologicalRing k] (hs : IsSmooth π) (v : V) :
    IsLocallyConstant fun g : GL (Fin N) k => π g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  refine Filter.mem_of_superset (((hs v).preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
  have hx' : π (g⁻¹ * x) v = v := hx
  show π x v = π g v
  conv_rhs => rw [← hx', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem isSqIntCoeff_of_isSquareIntegrable {δ : IrrGL k} (h : UnitaryDual.IsSquareIntegrable δ) :
    IsSqIntCoeff δ.rep := by
  obtain ⟨-, hu, ν, hν, H⟩ := h
  intro m hm μ hμ v l hl
  obtain rfl : m = _root_.borel _ := hm.measurable_eq
  letI : MeasurableSpace (AdGL k δ.1) := _root_.borel _
  have := secondCountableTopology_GL k (Fin δ.1)
  have hs := δ.2.rep.smooth
  have hF := norm_coeff_out hs δ.2.rep.irr hu v l
  have hl' : l ∈ smoothPart δ.rep.dual := hl.preimage continuous_inv
  refine ⟨fun q => ‖l (δ.rep q.out v)‖, hF, ?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k δ.1 => ‖l (δ.rep q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (δ.rep g v)‖ from funext hF]
    exact ((isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  · rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
      Measure.isMulLeftInvariant_eq_smul μ ν, lintegral_smul_measure]
    have h1 := H v l hl'
    simp only [enorm_norm, ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h1

end GlobalTheory.LocGL.SqIntBridge

namespace GlobalTheory.Published

theorem squareIntegrableSegment_of_ess (h : EssSquareIntegrableSegments) : SquareIntegrableSegment := by
  intro k _ _ _ _ _ δ hδ
  refine (h k δ hδ.1).1 ⟨1, isSmoothChar_one, ?_⟩
  rw [IrrGL.tw_one]
  exact SqIntBridge.isSqIntCoeff_of_isSquareIntegrable hδ

end GlobalTheory.Published

end
