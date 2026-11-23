import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBorelSectionUnitaryOrbitQuadric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabiliserCutoff

variable {P Q : ℕ}

theorem qf_eq (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.qf x = PerpendicularEmbedding.qf x := by
  have h : ActionCoordinates.herm x x = PerpendicularEmbedding.herm x x := by
    simp [ActionCoordinates.herm, PerpendicularEmbedding.herm, ActionCoordinates.sgn, Fintype.sum_sum_type, sub_eq_add_neg]
  rw [ActionCoordinates.qf, h, PerpendicularEmbedding.herm_self, Complex.ofReal_re]

theorem qf_act (g : UpqT P Q) (x : PerpendicularEmbedding.Sp P Q) : PerpendicularEmbedding.qf (ActionCoordinates.act g x) = PerpendicularEmbedding.qf x := by
  have h : (PerpendicularEmbedding.qf (ActionCoordinates.act g x) : ℂ) = PerpendicularEmbedding.qf x := by
    rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self, ActionCoordinates.act, star_mulVec,
      mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      GlobalTheory.UpqTopology.mat_unitary]
  exact_mod_cast h

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem continuous_act (x : ActionCoordinates.Wsp P Q) : Continuous fun g : UpqT P Q => ActionCoordinates.act g x :=
  GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

theorem eq_zero_of_herm {v : ActionCoordinates.Wsp P Q} (h : ∀ w, ActionCoordinates.herm v w = 0) : v = 0 := by
  funext i
  have := h (Pi.single i 1)
  rcases i with i | i <;>
    simpa [ActionCoordinates.herm, ActionCoordinates.sgn, Pi.single_apply, apply_ite] using this

theorem exists_cutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 →
    ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
    ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} →
    ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧
      ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  intro c P Q P' Q' x₀ h0 j ι hι hr
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  haveI := c.haar P' Q'
  haveI := GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure P' Q' _ (c.haar P' Q')
  obtain ⟨s, hsm, hs⟩ := GlobalTheory.QuadricSection.exists_isSection P Q _ x₀ (qf_eq x₀ ▸ h0) rfl
  obtain ⟨L, hL⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot'.2 fun v hv =>
    eq_zero_of_herm fun w => by rw [← hι.1, hv]; simp [ActionCoordinates.herm])
  have hL' : ∀ v, L (j v) = v := fun v => LinearMap.congr_fun hL v
  let Φ : UpqT P' Q' → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun h b => ActionCoordinates.act h (Pi.single b 1)
  let π : UpqT P Q → (Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q' :=
    fun g b => L (ActionCoordinates.act g (j (Pi.single b 1)))
  have hΦ : Continuous Φ := continuous_pi fun b => continuous_act _
  have hπ : Continuous π := continuous_pi fun b =>
    L.continuous_of_finiteDimensional.comp (continuous_act _)
  have hΦi : Function.Injective Φ := fun a b hab =>
    GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective (by
      ext x y
      simpa [Φ, ActionCoordinates.act] using congrFun (congrFun hab y) x)
  have hπι : ∀ a b, π (ι a * ι b) = Φ (a * b) := fun a b => by
    funext x
    simp only [π, Φ, act_mul, (hι.2.2 _).2, hL']
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P' Q')
  have hpos : c.cd P' Q' K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK1).ne'
  have hfin : c.cd P' Q' K ≠ ⊤ := hK.measure_lt_top.ne
  have hO : MeasurableSet (Φ '' K) := (hK.image hΦ).isClosed.measurableSet
  let F : ((Fin P' ⊕ Fin Q') → ActionCoordinates.Wsp P' Q') → ℝ≥0∞ :=
    (Φ '' K).indicator fun _ => (c.cd P' Q' K)⁻¹
  have hF : Measurable F := measurable_const.indicator hO
  have hFΦ : ∀ h, F (Φ h) = K.indicator (fun _ => (c.cd P' Q' K)⁻¹) h := fun h => by
    by_cases hh : h ∈ K
    · simp only [F, Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mem_image_of_mem Φ hh)]
    · simp only [F, Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (mt hΦi.mem_set_image.1 hh)]
  refine ⟨fun g => F (π (g * s (ActionCoordinates.act g⁻¹ x₀))), ?_, fun g => ?_⟩
  · exact hF.comp (hπ.measurable.comp (measurable_id.mul
      (hsm.comp ((continuous_act x₀).comp continuous_inv).measurable)))
  · obtain ⟨h₀, hh₀⟩ : g * s (ActionCoordinates.act g⁻¹ x₀) ∈ Set.range ι := by
      rw [hr]
      change ActionCoordinates.act (g * s (ActionCoordinates.act g⁻¹ x₀)) x₀ = x₀
      have e : ActionCoordinates.act (s (ActionCoordinates.act g⁻¹ x₀)) x₀ = ActionCoordinates.act g⁻¹ x₀ := hs _ (qf_act _ _)
      rw [act_mul, e, ← act_mul, mul_inv_cancel, act_one]
    have e : ∀ h, F (π (ι h * g * s (ActionCoordinates.act (ι h * g)⁻¹ x₀))) = F (Φ (h * h₀)) := fun h => by
      have e1 : ActionCoordinates.act (ι h)⁻¹ x₀ = x₀ := by
        conv_lhs => rw [← (hι.2.2 h).1, ← act_mul, inv_mul_cancel, act_one]
      rw [_root_.mul_inv_rev, act_mul, e1, mul_assoc, ← hh₀, hπι]
    simp only [e]
    refine ⟨hF.comp (hΦ.measurable.comp (measurable_mul_const h₀)), ?_⟩
    rw [lintegral_mul_right_eq_self (fun h => F (Φ h)) h₀]
    simp only [hFΦ]
    rw [lintegral_indicator_const hK.isClosed.measurableSet, ENNReal.inv_mul_cancel hpos hfin]

end GlobalTheory.StabiliserCutoff
