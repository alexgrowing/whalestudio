import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

noncomputable section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.Gen.SplitAE

variable (G : GDatum)

def toCenter : 𝓞 G.F →+* Subring.center (ℚ ⊗[ℤ] G.O) where
  toFun c := ⟨(1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c, Subring.mem_center_iff.mpr fun g => by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul q o => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.commutes]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]⟩
  map_one' := by ext; simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by ext; simp [Algebra.TensorProduct.tmul_mul_tmul]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [TensorProduct.tmul_add]

theorem toCenter_isUnit (c : nonZeroDivisors (𝓞 G.F)) : IsUnit (toCenter G c) := by
  have hc0 : (c : 𝓞 G.F) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hI := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self (c : 𝓞 G.F))
    (Algebra.IsIntegral.isIntegral (R := ℤ) (c : 𝓞 G.F))
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hu : IsUnit ((k : Subring.center (ℚ ⊗[ℤ] G.O))) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap ℚ _ (k : ℚ)⁻¹,
      Subring.mem_center_iff.mpr fun g => (Algebra.commutes _ g).symm⟩, ?_⟩
    apply Subtype.ext
    show ((k : Subring.center (ℚ ⊗[ℤ] G.O)) : ℚ ⊗[ℤ] G.O) * algebraMap ℚ _ (k : ℚ)⁻¹ = 1
    rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] G.O)), ← map_mul, mul_inv_cancel₀ hk', map_one]
  have hm : toCenter G d * toCenter G c = (k : Subring.center (ℚ ⊗[ℤ] G.O)) := by
    rw [← map_mul, hd, eq_intCast (algebraMap ℤ (𝓞 G.F)) k, map_intCast]
  exact isUnit_of_mul_isUnit_right (hm ▸ hu)

def fMap : G.F →+* ℚ ⊗[ℤ] G.O :=
  (Subring.center (ℚ ⊗[ℤ] G.O)).subtype.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G))

theorem fMap_mem_center (x : G.F) : fMap G x ∈ Subring.center (ℚ ⊗[ℤ] G.O) :=
  (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G) x).2

instance instAlgebraF : Algebra G.F (ℚ ⊗[ℤ] G.O) :=
  (fMap G).toAlgebra' fun x y => ((Subring.mem_center_iff.mp (fMap_mem_center G x)) y).symm

theorem algebraMap_F_coe (c : 𝓞 G.F) :
    algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) = (1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c := by
  show fMap G (algebraMap (𝓞 G.F) G.F c) = _
  simp only [fMap, RingHom.comp_apply, IsLocalization.lift_eq]
  rfl

instance instTowerF : IsScalarTower ℚ G.F (ℚ ⊗[ℤ] G.O) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ (ℚ ⊗[ℤ] G.O)) ((algebraMap G.F (ℚ ⊗[ℤ] G.O)).comp (algebraMap ℚ G.F))
    exact congrArg (fun f : ℚ →+* ℚ ⊗[ℤ] G.O => f q) this

def ordB : Subring (ℚ ⊗[ℤ] G.O) := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom.range

end GlobalTheory.UPel.HT.Gen.SplitAE
