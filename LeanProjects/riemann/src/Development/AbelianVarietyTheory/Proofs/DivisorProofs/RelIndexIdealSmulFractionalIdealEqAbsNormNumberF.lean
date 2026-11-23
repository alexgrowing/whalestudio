import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.FracIdealIndex

theorem relIndex_smul_eq_absNorm : ∀ (F : Type) [Field F] [NumberField F] (I : Submodule (𝓞 F) F) (p : Ideal (𝓞 F)), p ≠ ⊥ → I ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (p • I).toAddSubgroup.relIndex I.toAddSubgroup = Ideal.absNorm p := by
  intro F _ _ I p hp hI ⟨c, hc0, hc⟩
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc0
  let f : F →ₗ[𝓞 F] F := c • LinearMap.id
  have hf : ∀ y, f y = c • y := fun y => rfl
  have hfi : Function.Injective f := fun y z h => by
    simp only [hf, Algebra.smul_def] at h
    exact mul_left_cancel₀ (by simpa using hc') h
  let g : 𝓞 F →ₗ[𝓞 F] F := Algebra.linearMap (𝓞 F) F
  have hgi : Function.Injective g := fun y z h => by
    simpa [g] using h
  have hle : Submodule.map f I ≤ LinearMap.range g := by
    rw [← Submodule.one_eq_range]
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  let J : Ideal (𝓞 F) := (Submodule.map f I).comap g
  have hJ : Submodule.map g J = Submodule.map f I := Submodule.map_comap_eq_of_le hle
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply hI
    have : Submodule.map f I = ⊥ := by rw [← hJ, h, Submodule.map_bot]
    exact Submodule.map_injective_of_injective hfi (this.trans (Submodule.map_bot f).symm)
  have hpJ : Submodule.map g (p * J) = Submodule.map f (p • I) := by
    rw [← Ideal.smul_eq_mul, Submodule.map_smul'', Submodule.map_smul'', hJ]
  have e1 : (p • I).toAddSubgroup.relIndex I.toAddSubgroup =
      (p * J).toAddSubgroup.relIndex J.toAddSubgroup := by
    have a1 := AddSubgroup.relIndex_map_map_of_injective (p • I).toAddSubgroup I.toAddSubgroup
      (f := (f : F →+ F)) hfi
    have a2 := AddSubgroup.relIndex_map_map_of_injective (p * J).toAddSubgroup J.toAddSubgroup
      (f := (g : 𝓞 F →+ F)) hgi
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup] at a1 a2
    rw [← a1, ← a2, hpJ, hJ]
  have hle2 : p * J ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
  have hidx : (p * J).toAddSubgroup.relIndex J.toAddSubgroup * Ideal.absNorm J = Ideal.absNorm (p * J) :=
    AddSubgroup.relIndex_mul_index (H := (p * J).toAddSubgroup) (K := J.toAddSubgroup) hle2
  have hN : Ideal.absNorm J ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hJ0
  rw [e1]
  rw [map_mul] at hidx
  exact mul_right_cancel₀ hN hidx

end GlobalTheory.FracIdealIndex
