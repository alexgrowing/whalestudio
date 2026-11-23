import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ConeHaar

theorem continuous_hOf (n : ℕ) : Continuous (hOf : (Fin n × Fin n → ℝ) → Mat n) := by
  unfold hOf
  fun_prop

theorem isClosed_posSemidef (n : ℕ) : IsClosed {M : Mat n | M.PosSemidef} := by
  have h : {M : Mat n | M.PosSemidef} =
      {M : Mat n | Mᴴ = M} ∩ ⋂ x : Fin n → ℂ, {M : Mat n | 0 ≤ star x ⬝ᵥ M *ᵥ x} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [h]
  refine IsClosed.inter (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id) ?_
  refine isClosed_iInter fun x => isClosed_le continuous_const ?_
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

theorem measurableSet_cone (n : ℕ) : MeasurableSet (cone n) := by
  have h : cone n = (hOf ⁻¹' {M : Mat n | M.PosSemidef}) ∩
      ((fun v => (hOf v : Mat n).det) ⁻¹' {(0 : ℂ)}ᶜ) := by
    ext v
    simp only [cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun hv => ⟨hv.posSemidef, hv.det_pos.ne'⟩,
      fun hv => (Matrix.PosSemidef.posDef_iff_det_ne_zero hv.1).2 hv.2⟩
  rw [h]
  refine MeasurableSet.inter ((isClosed_posSemidef n).preimage (continuous_hOf n)).measurableSet ?_
  exact (isClosed_singleton.isOpen_compl.preimage
    (continuous_hOf n).matrix_det).measurableSet

theorem measurable_coneW (n : ℕ) : Measurable (coneW n) := by
  have h : Continuous fun v : Fin n × Fin n → ℝ => (hOf v : Mat n).det.re :=
    Complex.continuous_re.comp (continuous_hOf n).matrix_det
  unfold coneW
  exact ((h.measurable.pow_const n).inv).ennreal_ofReal

theorem coneW_toReal_smul (n : ℕ) (f : (Fin n × Fin n → ℝ) → ℂ) {v : Fin n × Fin n → ℝ}
    (hv : v ∈ cone n) : (coneW n v).toReal • f v = f v * ((hOf v).det ^ n)⁻¹ := by
  have hpos : (0 : ℂ) < (hOf v : Mat n).det := Matrix.PosDef.det_pos hv
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
  have hdet : (hOf v : Mat n).det = (((hOf v : Mat n).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using him.symm)
  have hnn : 0 ≤ ((hOf v : Mat n).det.re ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hre.le n)
  unfold coneW
  rw [ENNReal.toReal_ofReal hnn, Complex.real_smul, mul_comm]
  congr 1
  conv_rhs => rw [hdet]
  push_cast
  rfl

theorem cone_integral : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  intro n
  refine ⟨?_, fun f => ?_⟩
  · exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurableSet_cone n))
  · unfold coneMeas
    rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_coneW n).aemeasurable
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) f]
    exact setIntegral_congr_fun (measurableSet_cone n) fun v hv => coneW_toReal_smul n f hv

end GlobalTheory.CompanionTheory.ConeHaar
