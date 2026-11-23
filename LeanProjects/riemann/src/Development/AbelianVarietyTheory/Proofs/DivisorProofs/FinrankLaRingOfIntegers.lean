import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

theorem Datum.finrank_La_ringOfIntegers :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p),
      letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O);
      Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  intro p _ D
  letI iL : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  letI iV : Module (𝓞 D.F) D.VF := Module.compHom D.VF (algebraMap (𝓞 D.F) D.F)
  haveI : IsScalarTower (𝓞 D.F) D.F D.VF :=
    ⟨fun c x v => by
      show (algebraMap (𝓞 D.F) D.F c * x) • v = algebraMap (𝓞 D.F) D.F c • (x • v)
      rw [mul_smul]⟩
  let f : D.La →ₗ[𝓞 D.F] D.VF :=
    { toFun := fun z => (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF)
      map_add' := fun z w => TensorProduct.tmul_add _ _ _
      map_smul' := fun c z => by
        rw [RingHom.id_apply]
        show (((1 : ℚ) ⊗ₜ (algebraMap (𝓞 D.F) D.O c • z) : D.VQ) : D.VF) =
          algebraMap (𝓞 D.F) D.F c • (show D.VF from (1 : ℚ) ⊗ₜ z)
        rw [D.smul_VF, show algebraMap (𝓞 D.F) D.F c = (c : D.F) from rfl, D.actF_coe, D.coe_actInt]
        rfl }
  have hf : ∀ z, f z = (((1 : ℚ) ⊗ₜ z : D.VQ) : D.VF) := fun _ => rfl

  have hnat : ∀ (n : ℕ) (v : D.VF), ((n : 𝓞 D.F)) • v = n • v := by
    intro n v
    show algebraMap (𝓞 D.F) D.F (n : 𝓞 D.F) • v = n • v
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 D.F)) f := by
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : (c : D.F) ≠ 0 := by
        intro h
        exact (mem_nonZeroDivisors_iff_ne_zero.1 hc) (by exact_mod_cast h)
      rw [Module.End.isUnit_iff]
      constructor
      · intro v w h
        have h' : (c : D.F) • v = (c : D.F) • w := h
        exact smul_right_injective D.VF hc0 h'
      · intro v
        refine ⟨(c : D.F)⁻¹ • v, ?_⟩
        show (c : D.F) • ((c : D.F)⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    · intro y
      obtain ⟨q, z, -, hy⟩ := D.exists_tmul y
      have hd : ((q.den : ℕ) : 𝓞 D.F) ∈ nonZeroDivisors (𝓞 D.F) :=
        mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast q.den_ne_zero)
      refine ⟨(q.num • z, ⟨_, hd⟩), ?_⟩
      show ((q.den : ℕ) : 𝓞 D.F) • y = f (q.num • z)
      rw [hnat, hf, hy]
      show q.den • (q ⊗ₜ z : D.VQ) = ((1 : ℚ) ⊗ₜ (q.num • z) : D.VQ)
      rw [TensorProduct.smul_tmul', nsmul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_one]
    · intro z w h
      rw [hf, hf] at h
      obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ)
        (TensorProduct.mk ℤ ℚ D.La 1)).1 h
      have hc0 : ((c : ℤ) : 𝓞 D.F) ≠ 0 := by
        exact_mod_cast mem_nonZeroDivisors_iff_ne_zero.1 hc
      refine ⟨⟨_, mem_nonZeroDivisors_of_ne_zero hc0⟩, ?_⟩
      show algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • z = algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F) • w
      rw [map_intCast, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact hcz
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 D.F)) f le_rfl
  have h2 := IsFractionRing.finrank_right_eq (𝓞 D.F) D.F D.VF
  rw [← h1, ← h2, D.finrank_VF]

end GlobalTheory.UPel.HT
