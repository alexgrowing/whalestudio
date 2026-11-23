import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteTensor
set_option maxSynthPendingDepth 1

noncomputable section

open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange

namespace GroundTheory.BlockD

namespace ThmBHecke

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def adeleEquiv : AE F E ≃ₐ[AF F] 𝔸[E] := adeleTensorAlgEquivLeft F E

theorem adeleEquiv_tmul (a : AF F) (x : E) :
    adeleEquiv F E (a ⊗ₜ x) = algebraMap E 𝔸[E] x * adeleMap F E a :=
  adeleTensorAlgEquivLeft_tmul a x

theorem adeleEquiv_incA (x : E) : adeleEquiv F E (incA F E x) = algebraMap E 𝔸[E] x := by
  change adeleEquiv F E (1 ⊗ₜ x) = _
  rw [adeleEquiv_tmul, map_one, mul_one]

theorem adeleEquiv_algebraMap (a : AF F) :
    adeleEquiv F E (algebraMap (AF F) (AE F E) a) = adeleMap F E a :=
  (adeleEquiv F E).commutes a

instance isModuleTopology_AE : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩

theorem continuous_adeleEquiv : Continuous (adeleEquiv F E) := by
  have := isModuleTopology_adeleRing (K := F) (L := E)
  exact IsModuleTopology.continuous_of_linearMap (adeleEquiv F E).toLinearMap

theorem continuous_adeleEquiv_symm : Continuous (adeleEquiv F E).symm := by
  have := isModuleTopology_adeleRing (K := F) (L := E)
  have := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  exact IsModuleTopology.continuous_of_linearMap (adeleEquiv F E).symm.toLinearMap

variable (F E) in

def ideleEquiv : (AE F E)ˣ ≃* IdeleGroup E :=
  Units.mapEquiv (adeleEquiv F E).toRingEquiv.toMulEquiv

@[simp]
theorem coe_ideleEquiv (x : (AE F E)ˣ) : ((ideleEquiv F E x : IdeleGroup E) : 𝔸[E]) = adeleEquiv F E x :=
  rfl

@[simp]
theorem coe_ideleEquiv_symm (x : IdeleGroup E) :
    (((ideleEquiv F E).symm x : (AE F E)ˣ) : AE F E) = (adeleEquiv F E).symm x :=
  rfl

theorem continuous_ideleEquiv_symm : Continuous (ideleEquiv F E).symm :=
  Units.continuous_iff.2 ⟨continuous_adeleEquiv_symm.comp Units.continuous_val,
    continuous_adeleEquiv_symm.comp Units.continuous_coe_inv⟩

variable (F E) in

def finEquiv : Af F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E :=
  (Algebra.TensorProduct.comm F (Af F) E).toRingEquiv.trans (finiteTensorEquiv F E).toRingEquiv

theorem finEquiv_tmul (a : Af F) (x : E) :
    finEquiv F E (a ⊗ₜ x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x * finiteAdeleMap F E a := by
  change finiteTensorEquiv F E (Algebra.TensorProduct.comm F (Af F) E (a ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul, finiteTensorEquiv_tmul]

theorem finEquiv_one_tmul (x : E) :
    finEquiv F E (1 ⊗ₜ x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := by
  rw [finEquiv_tmul, map_one, mul_one]

theorem adeleEquiv_snd (z : AE F E) : (adeleEquiv F E z).2 = finEquiv F E (finPart F E z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    rfl
  | tmul a x =>
    rw [adeleEquiv_tmul]
    change (algebraMap E 𝔸[E] x).2 * (adeleMap F E a).2 = finEquiv F E (sndA F a ⊗ₜ x)
    rw [finEquiv_tmul]
    rfl
  | add y z hy hz =>
    rw [map_add, map_add, map_add, ← hy, ← hz]
    rfl

theorem finEquiv_symm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (t : FiniteAdeleRing (𝓞 E) E) :
    (finEquiv F E).symm t = ∑ i, finiteCoord b i t ⊗ₜ b i := by
  change (Algebra.TensorProduct.comm F (Af F) E).symm ((finiteTensorEquiv F E).symm t) = _
  rw [finiteTensorEquiv_symm_apply b, map_sum]
  rfl

theorem algebraMap_mem_integralFiniteAdeles (x : 𝓞 E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E) ∈ integralFiniteAdeles (𝓞 E) E := fun w ↦
  (coe_mem_adicCompletionIntegers_iff w (x : E)).2 (w.valuation_le_one x)

theorem finiteAdeleMap_mem_integralFiniteAdeles {a : Af F} (ha : a ∈ intAf F) :
    finiteAdeleMap F E a ∈ integralFiniteAdeles (𝓞 E) E := fun w ↦ by
  rw [finiteAdeleMap_apply]
  exact mapsTo_completionMap _ w (ha _)

theorem finEquiv_mem_of_mem_intAE {y : Af F ⊗[F] E} (hy : y ∈ intAE F E) :
    finEquiv F E y ∈ integralFiniteAdeles (𝓞 E) E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    rw [finEquiv_tmul]
    exact Subring.mul_mem _ (algebraMap_mem_integralFiniteAdeles x)
      (finiteAdeleMap_mem_integralFiniteAdeles ha)
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact Subring.add_mem _ h1 h2
  | neg _ _ h => rw [map_neg]; exact Subring.neg_mem _ h

theorem exists_basis_isIntegral :
    ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  classical
  set c := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image c)
  have hu : ∀ _ : Fin (Module.finrank F E), IsUnit ((y : F)) := fun _ ↦
    (Int.cast_ne_zero.2 hy0).isUnit
  refine ⟨c.isUnitSMul hu, fun i ↦ ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
  exact hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem mem_integralFiniteAdeles_mul_of_isIntegral {s : FiniteAdeleRing (𝓞 E) E}
    (hs : s ∈ integralFiniteAdeles (𝓞 E) E) {x : E} (hx : IsIntegral ℤ x) (w : HeightOneSpectrum (𝓞 E)) :
    s w * algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  Subring.mul_mem _ (hs w) (algebraMap_mem_integralFiniteAdeles (⟨x, hx⟩ : 𝓞 E) w)

theorem mem_intAE_of_mem_integralFiniteAdeles {t : FiniteAdeleRing (𝓞 E) E}
    (ht : t ∈ integralFiniteAdeles (𝓞 E) E) : (finEquiv F E).symm t ∈ intAE F E := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_isIntegral (F := F) (E := E)
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image (traceDual b))

  have hcoord : ∀ s ∈ integralFiniteAdeles (𝓞 E) E,
      (finEquiv F E).symm ((D : FiniteAdeleRing (𝓞 E) E) * s) ∈ intAE F E := by
    intro s hs
    rw [finEquiv_symm_eq_sum b]
    refine AddSubgroup.sum_mem _ fun i _ ↦ AddSubgroup.subset_closure
      ⟨finiteCoord b i ((D : FiniteAdeleRing (𝓞 E) E) * s), fun v ↦ ?_, ⟨b i, hb i⟩, rfl⟩
    change localCoord b v i _ ∈ _
    refine localCoord_mem b v i _ fun w ↦ ?_
    have h := mem_integralFiniteAdeles_mul_of_isIntegral hs
      (hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) w.1
    have he : ((D : FiniteAdeleRing (𝓞 E) E) * s) w.1 * algebraMap E (w.1.adicCompletion E) (traceDual b i)
        = s w.1 * algebraMap E (w.1.adicCompletion E) (D • traceDual b i) := by
      rw [zsmul_eq_mul, map_mul, map_intCast]
      change ((D : w.1.adicCompletion E) * s w.1) * _ = _
      ring
    rw [he]
    exact h

  have hDE : (D : E) ≠ 0 := Int.cast_ne_zero.2 hD0
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 E) (K := E)
    (t * algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E)⁻¹)
  set s := t * algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E)⁻¹ - algebraMap E _ k with hs
  have hDc : (D : FiniteAdeleRing (𝓞 E) E) = algebraMap E (FiniteAdeleRing (𝓞 E) E) (D : E) := by
    rw [map_intCast]
  have htk : t = algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) +
      (D : FiniteAdeleRing (𝓞 E) E) * s := by
    rw [hs, hDc, mul_sub, ← mul_assoc, mul_comm (algebraMap E _ (D : E)) t, mul_assoc, ← map_mul,
      mul_inv_cancel₀ hDE, map_one, mul_one, map_mul]
    ring
  have hDk : (D : E) * k ∈ (algebraMap (𝓞 E) E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (K := E) _ fun w ↦ ?_
    rw [← coe_mem_adicCompletionIntegers_iff]
    have h1 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) ∈ integralFiniteAdeles (𝓞 E) E := by
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k) =
          t - (D : FiniteAdeleRing (𝓞 E) E) * s := by
        rw [htk]; ring
      rw [h2]
      refine Subring.sub_mem _ ht (Subring.mul_mem _ ?_ hk)
      rw [hDc]
      exact algebraMap_mem_integralFiniteAdeles (D : 𝓞 E)
    exact h1 w
  obtain ⟨z, hz⟩ := hDk
  rw [htk, map_add]
  refine AddSubgroup.add_mem _ ?_ (hcoord s hk)
  have h1 : (finEquiv F E).symm (algebraMap E (FiniteAdeleRing (𝓞 E) E) ((D : E) * k)) =
      (1 : Af F) ⊗ₜ[F] ((z : 𝓞 E) : E) := by
    rw [RingEquiv.symm_apply_eq, finEquiv_one_tmul, ← hz]
  rw [h1]
  exact AddSubgroup.subset_closure ⟨1, fun v ↦ Subring.one_mem _, z, rfl⟩

theorem mem_intAE_iff (y : Af F ⊗[F] E) :
    y ∈ intAE F E ↔ finEquiv F E y ∈ integralFiniteAdeles (𝓞 E) E :=
  ⟨finEquiv_mem_of_mem_intAE, fun h ↦ by
    simpa using mem_intAE_of_mem_integralFiniteAdeles (F := F) h⟩

end ThmBHecke

end GroundTheory.BlockD
