import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.FibrePositive

theorem act_mul {P Q : ℕ} (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  have : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl
  simp only [ActionCoordinates.act, this, Matrix.mulVec_mulVec]

theorem act_one {P Q : ℕ} (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := by
  have : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  simp only [ActionCoordinates.act, this, Matrix.one_mulVec]

theorem act_inv_of_fix {P Q : ℕ} {g : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (h : ActionCoordinates.act g x = x) :
    ActionCoordinates.act g⁻¹ x = x := by
  conv_lhs => rw [← h]
  rw [← act_mul, inv_mul_cancel, act_one]

theorem fibre_lintegral_ne_zero : ActionCoordinates.QuotientMeasure → CDHaar → ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x₀ = β → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : ActionCoordinates.Wsp P Q → ℝ, Continuous φ → 0 < φ x₀ → ∫⁻ y, ENNReal.ofReal (φ y) ∂(fib β) ≠ 0 := by
  intro hQ c P Q β hβ x₀ hx₀ fib hfib φ hφ hpos h0
  obtain ⟨h1, ⟨P', Q', j, ι, -, -, hfr⟩, h3⟩ := hQ P Q β hβ x₀ hx₀
  obtain ⟨htop, -, -, -, hbor, hcl⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  classical
  choose s0 hs0 using h1
  let s : ActionCoordinates.Wsp P Q → UpqT P Q := fun y => if h : ActionCoordinates.qf y = β then s0 y h else 1
  have hs : ∀ y, ActionCoordinates.qf y = β → ActionCoordinates.act (s y)⁻¹ x₀ = y := by
    intro y hy
    simp only [s, dif_pos hy]
    exact hs0 y hy
  have hc : Continuous fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x₀ :=
    (hcl.continuous.comp continuous_inv).matrix_mulVec continuous_const
  have hfc : Continuous fun g : UpqT P Q => ENNReal.ofReal (φ (ActionCoordinates.act g⁻¹ x₀)) :=
    ENNReal.continuous_ofReal.comp (hφ.comp hc)
  have key := (h3 P' Q' j ι hfr).2 c fib hfib s hs _ hfc.measurable
  have hφm : Measurable fun y => ENNReal.ofReal (φ y) :=
    (ENNReal.continuous_ofReal.comp hφ).measurable
  have hae := (lintegral_eq_zero_iff hφm).1 h0
  have hqm : MeasurableSet {y : ActionCoordinates.Wsp P Q | ActionCoordinates.qf y = β} := by
    have : Continuous (ActionCoordinates.qf : ActionCoordinates.Wsp P Q → ℝ) := by
      unfold ActionCoordinates.qf ActionCoordinates.herm
      fun_prop
    exact (isClosed_eq this continuous_const).measurableSet
  have hR : ∫⁻ y in {y | ActionCoordinates.qf y = β}, (∫⁻ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀))
      ∂(c.cd P' Q')) ∂(fib β) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hqm] with y hy hq
    have : ∀ g', ENNReal.ofReal (φ (ActionCoordinates.act (ι g' * s y)⁻¹ x₀)) = 0 := by
      intro g'
      rw [_root_.mul_inv_rev, act_mul, act_inv_of_fix (hfr.2.2 g').1, hs y hq]
      exact hy
    simp only [this, lintegral_zero, Pi.zero_apply]
  rw [hR, mul_zero] at key
  have := c.haar P Q
  have hz := (hfc.ae_eq_iff_eq (c.cd P Q) continuous_const).1 ((lintegral_eq_zero_iff hfc.measurable).1 key)
  have h1 : ENNReal.ofReal (φ (ActionCoordinates.act (1 : UpqT P Q)⁻¹ x₀)) = 0 := congrFun hz 1
  rw [inv_one, act_one, ENNReal.ofReal_eq_zero] at h1
  linarith

end GlobalTheory.FibrePositive
