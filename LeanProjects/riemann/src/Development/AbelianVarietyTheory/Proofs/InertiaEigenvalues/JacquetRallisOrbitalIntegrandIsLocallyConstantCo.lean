import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProperStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDetStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbTest

theorem eta_eq_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  unfold eta
  by_cases hx : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [if_pos hx, if_pos (h ▸ hx)]
  · rw [if_neg hx, if_neg (h ▸ hx)]

theorem isLocallyConstant_eta_comp {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')

theorem continuous_act {r : ℕ} {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] (Y : Gl r k) :
    Continuous (fun g : GL (Fin r) k => act g Y) := by
  unfold act
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const))
  · exact (Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv
  · exact Units.continuous_val.matrix_mulVec continuous_const
  · exact continuous_const.matrix_vecMul Units.continuous_coe_inv

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  unfold actU
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem continuous_actU {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E] [ContinuousStar E] (X : Hn r F E) :
    Continuous (fun g : Matrix.unitaryGroup (Fin r) E => actU g X) := by
  unfold actU
  refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
  · exact (continuous_subtype_val.matrix_mul continuous_const).matrix_mul continuous_subtype_val.star
  · exact continuous_subtype_val.matrix_mulVec continuous_const

end GlobalTheory.JR.OrbTest

namespace GlobalTheory.JR.OrbTest

theorem isTest_orbG_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f' : Gl r F → ℂ) (hf : IsTest f') (Y : Gl r F)
    (hY : Delta (inv Y) ≠ 0) :
    IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y)) := by
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨-, hL1b, hL1c, hL1d, hL1e⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  obtain ⟨hL6a, hL6b⟩ := GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det F r
  obtain ⟨-, -, -, hL4⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hC : (Cm Y).det ≠ 0 := by
    intro h0; apply hY; rw [Delta, ← hL1c Y, Matrix.det_mul, h0, zero_mul]
  have hld : (fun g : GL (Fin r) F => lastDet (act g Y)) = fun g =>
      (-1) ^ r * ((Cm Y).det * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) := by
    funext g; rw [hL6a, hL6b, Matrix.det_mul]
  refine ⟨?_, ?_⟩
  · refine IsLocallyConstant.comp₂ (hf.1.comp_continuous (continuous_act Y)) ?_ (fun a b => a * b)
    show IsLocallyConstant (fun g : GL (Fin r) F => eta (lastDet (act g Y)))
    refine isLocallyConstant_eta_comp (fun g : GL (Fin r) F => lastDet (act g Y)) ?_ ?_
    · rw [hld]
      exact continuous_const.mul (continuous_const.mul Units.continuous_coe_inv.matrix_det)
    · intro g
      rw [show lastDet (act g Y) = _ from congrFun hld g]
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hC ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹).isUnit).ne_zero
  · have ha : Delta (inv (sec (inv Y))) ≠ 0 := by rw [hL1b]; exact hY
    obtain ⟨g₀, ⟨hg₀, -⟩, -⟩ := hL1e (sec (inv Y)) Y ha (hL1b _).symm
    have hS : IsCompact {h : GL (Fin r) F | act h (sec (inv Y)) ∈ tsupport f'} := by
      have := hL4 (tsupport f') {inv Y} hf.2 isCompact_singleton (by rintro b rfl; exact hY)
      convert this.image continuous_fst using 1
      ext h; constructor
      · intro hh; exact ⟨(h, inv Y), ⟨rfl, hh⟩, rfl⟩
      · rintro ⟨⟨h', a'⟩, ⟨ha', hc⟩, rfl⟩
        simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
    have hK : IsCompact {g : GL (Fin r) F | act g Y ∈ tsupport f'} := by
      have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
      convert this using 1
      ext g; simp [Homeomorph.coe_mulRight, hL1d, hg₀]
    refine HasCompactSupport.intro' hK ((isClosed_tsupport f').preimage (continuous_act Y)) ?_
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [image_eq_zero_of_notMem_tsupport hg, zero_mul]

theorem isTest_orbU_integrand (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, hL5iv⟩ := GlobalTheory.T.invariant_image_openClosed_local_sections F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg

end GlobalTheory.JR.OrbTest

open GlobalTheory.JR.OrbTest in

theorem GlobalTheory.JR.orb_integrand_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ Y : Gl r F, Delta (inv Y) ≠ 0 → IsTest (fun g : GL (Fin r) F => f' (act g Y) * omega (act g Y))) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a : Inv r F) (X : Hn r F E), Delta a ≠ 0 → HasInv X a → IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  intro F E _ _ _ _ _ r _
  exact ⟨fun f' hf Y hY => isTest_orbG_integrand F E r f' hf Y hY,
    fun f hf a X ha hX => isTest_orbU_integrand F E r f hf a X ha hX⟩
