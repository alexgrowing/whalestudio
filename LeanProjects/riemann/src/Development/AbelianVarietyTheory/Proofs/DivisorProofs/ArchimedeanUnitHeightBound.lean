import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormArchLeSupInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearMatrixStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

open scoped Classical in

theorem archUnit_act_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ C : ℝ, ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' _
  have evI_mul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 * b.1) = _
    exact map_mul _ _ _
  have evI_sub : ∀ a b : AF F, evI F (a - b) = evI F a - evI F b := fun a b => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 - b.1) = _
    exact map_sub _ _ _
  have evI_one : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have evI_realAd : ∀ t : ℝ, evI F (realAd F t) = algebraMap ℝ _ t := fun t => by
    simp only [evI, realAd, LinearMap.inl_apply, RingEquiv.apply_symm_apply]
  obtain ⟨K5, hK5, h5⟩ := GlobalTheory.T.arch_bound_linear_matrix F E n d (Fin n × Fin d) M.co.e.symm.toLinearMap
  obtain ⟨K3, hK3, h3⟩ := GlobalTheory.T.arch_bound_coordinates F E
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.T.arch_bound_linear_coordinates F E n d (Fin n × Fin d) M.co.e.toLinearMap
  refine ⟨K4 * (K3 * (n * d * K5)) + 1, fun p u hu => ?_⟩
  have hg : (1 : ℝ) ≤ ht p.1 := by
    have := one_le_heightGL F (p.1 : GL (Fin n) (AF F ⊗[F] E))
    exact_mod_cast this
  have hh : (1 : ℝ) ≤ ht p.2 := by
    have := one_le_heightGL F (p.2 : GL (Fin d) (AF F ⊗[F] E))
    exact_mod_cast this
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = (ht p.1 : ℝ) * ht p.2 := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (K4 * (K3 * (n * d * K5)) + 1) * H := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    have : 0 < H := by rw [hH]; nlinarith
    positivity
  obtain ⟨x, hx⟩ : ∃ x, x = actAB (cA σ) p u := ⟨_, rfl⟩
  have s1 : ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (u k l)‖ ≤ K5 * 1 := by
    have := h5 (M.co.e u) 1 zero_le_one (fun w i =>
      ⟨((GlobalTheory.T.norm_arch_le_sup_infinite F _).1 w).trans (hu.2 i).1, ((GlobalTheory.T.norm_arch_le_sup_infinite F _).1 w).trans (hu.2 i).2⟩)
    simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using this
  have s2 := GlobalTheory.T.arch_bound_unitary_action F E σ n d X.J W.J p u (K5 * 1) (by positivity) s1
  rw [← hx, ← hH] at s2
  have s3 : ∀ w k l r, ‖archAt F w ((coB F E).repr (x k l) r)‖ ≤ K3 * (n * d * H * (K5 * 1)) :=
    fun w k l r => h3 (x k l) _ (by positivity) (fun w τ => s2 w τ k l) r w
  have s4 := h4 x _ (by positivity) s3
  have hbound : K4 * (K3 * (n * d * H * (K5 * 1))) ≤ c := by
    have e1 : K4 * (K3 * (n * d * H * (K5 * 1))) = K4 * (K3 * (n * d * K5)) * H := by ring
    rw [e1, hc]
    exact mul_le_mul_of_nonneg_right (by linarith) hH0
  have s5 : ∀ i, ‖evI F ((M.co.e x).1 i)‖ ≤ c ∧ ‖evI F ((M.co.e x).2 i)‖ ≤ c := fun i =>
    ⟨(GlobalTheory.T.norm_arch_le_sup_infinite F _).2 c hcpos.le (fun w => ((s4 w i).1).trans hbound),
     (GlobalTheory.T.norm_arch_le_sup_infinite F _).2 c hcpos.le (fun w => ((s4 w i).2).trans hbound)⟩
  have key : ∀ a : AF F, evI F a = 0 → a • M.co.e x = 0 := by
    intro a ha
    have h0 : a • M.co.e u = 0 := by
      refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
      · exact (hu.1 j).1 a ha
      · exact (hu.1 j).2 a ha
    have hu0 : a • u = 0 := by
      have := congrArg M.co.e.symm h0
      rwa [map_smul, LinearEquiv.symm_apply_apply, map_zero] at this
    rw [← map_smul, hx]
    have : a • actAB (cA σ) p u = actAB (cA σ) p (a • u) := by
      simp only [actAB, Matrix.mul_smul, Matrix.smul_mul]
    rw [this, hu0]
    simp [actAB]
  have harch : IsArch (M.co.e x) := fun i =>
    ⟨fun a ha => by simpa using congrArg (fun z => z.1 i) (key a ha),
     fun a ha => by simpa using congrArg (fun z => z.2 i) (key a ha)⟩
  have hone : ∀ z : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), IsArch z → realAd F 1 • z = z := by
    intro z hz
    have h1 : evI F (1 - realAd F 1) = 0 := by
      rw [evI_sub, evI_one, evI_realAd, map_one, sub_self]
    have : (1 - realAd F 1) • z = 0 :=
      Prod.ext (funext fun j => (hz j).1 _ h1) (funext fun j => (hz j).2 _ h1)
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  refine ⟨c, hcpos.le, by rw [hc, hH], realAd F c⁻¹ • M.co.e x, ⟨isArch_smul harch _, fun i => ⟨?_, ?_⟩⟩, ?_⟩
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).1 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).1 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).1 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · show ‖evI F (realAd F c⁻¹ * (M.co.e x).2 i)‖ ≤ 1
    rw [evI_mul, evI_realAd, ← Algebra.smul_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos)]
    calc c⁻¹ * ‖evI F ((M.co.e x).2 i)‖ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (s5 i).2 (inv_pos.2 hcpos).le
      _ = 1 := inv_mul_cancel₀ hcpos.ne'
  · rw [smul_smul, realAd_mul, mul_inv_cancel₀ hcpos.ne', hone _ harch, hx]

end GlobalTheory.ThetaDecay

end
