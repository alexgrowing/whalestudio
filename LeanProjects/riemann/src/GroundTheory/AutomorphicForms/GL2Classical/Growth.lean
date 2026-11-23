import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.IsWeightLevelAdelicLift

open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm Filter Topology
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem norm_archLift (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    ‖archLift k f h‖ = Real.sqrt (h • I).im ^ k * ‖f (h • I)‖ := by
  have hj : denom h (I : ℂ) ≠ 0 := denom_ne_zero h I
  rw [archLift, norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), im_smul_I hpos, sqrt_div_normSq, div_zpow, _root_.zpow_neg,
    div_eq_mul_inv]
  ring

theorem norm_adelicLift (f : ℍ → ℂ) (g : AdelicGL ℚ 2) :
    ∃ z : ℍ, ‖adelicLift N k f g‖ = Real.sqrt z.im ^ k * ‖f z‖ :=
  ⟨decompGL N g • I, norm_archLift f (decompGL_spec N g).1⟩

theorem sqrt_zpow_eq_rpow {y : ℝ} (hy : 0 < y) (k : ℤ) : Real.sqrt y ^ k = y ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hy.le]
  congr 1
  ring

theorem exists_bound_liftEquiv_cuspForm (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ C, ∀ g, ‖(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) g‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun g => ?_⟩
  rw [liftEquiv_apply]
  obtain ⟨z, hz⟩ := norm_adelicLift (N := N) (k := k) (f.toSlashInvariantForm : ℍ → ℂ) g
  rw [hz]
  have hy := z.im_pos
  have hpow : 0 < z.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hy _
  have h1 : ‖(f.toSlashInvariantForm : ℍ → ℂ) z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := hC z
  rw [sqrt_zpow_eq_rpow hy]
  calc z.im ^ ((k : ℝ) / 2) * ‖(f.toSlashInvariantForm : ℍ → ℂ) z‖
      ≤ z.im ^ ((k : ℝ) / 2) * (C / z.im ^ ((k : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h1 hpow.le
    _ = C := by field_simp

theorem hasModerateGrowth_liftEquiv_cuspForm
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    HasModerateGrowth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  obtain ⟨C, hC⟩ := exists_bound_liftEquiv_cuspForm f
  exact ⟨C, 0, fun g => by rw [pow_zero, mul_one]; exact hC g⟩

theorem IsWeightLevel.eventually_finEmb {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsWeightLevel N k φ)
    (g : AdelicGL ℚ 2) : ∀ᶠ y in 𝓝 (1 : FiniteAdelicGL ℚ 2), φ (g * finEmb ℚ 2 y) = φ g :=
  Filter.mem_of_superset ((isOpen_Gamma0Level N).mem_nhds (one_mem _)) fun y hy =>
    hφ.right_level g y hy

end GL2Classical

end

end GroundTheory.Automorphic
