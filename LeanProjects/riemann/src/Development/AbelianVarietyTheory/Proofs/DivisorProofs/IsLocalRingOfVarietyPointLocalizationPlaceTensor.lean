import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

theorem exists_mul_mem_tens (E : Place (algebraMap ℂ K)) (w : K ⊗[ℂ] κ') :
    ∃ d ∈ E.ring, d ≠ 0 ∧ (d ⊗ₜ[ℂ] (1 : κ')) * w ∈ tens (κ' := κ') (placeAlg E) := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, one_ne_zero, by simpa using zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := E.isLocModel.frac x
    refine ⟨b, hb, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, e]
    exact tmul_mem ha y
  | add u v hu hv =>
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := hu
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := hv
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, mul_ne_zero hd₁0 hd₂0, ?_⟩
    have e : ((d₁ * d₂) ⊗ₜ[ℂ] (1 : κ')) * (u + v) =
        (d₂ ⊗ₜ[ℂ] (1 : κ')) * ((d₁ ⊗ₜ[ℂ] (1 : κ')) * u) +
          (d₁ ⊗ₜ[ℂ] (1 : κ')) * ((d₂ ⊗ₜ[ℂ] (1 : κ')) * v) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁, mul_add]
    rw [e]
    exact add_mem (mul_mem (tmul_mem hd₂ 1) h₁) (mul_mem (tmul_mem hd₁ 1) h₂)

theorem isLocModel_locAt : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ E 𝔭 _ hO
  obtain ⟨O', hO'⟩ := hO
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ locAt (L := L) 𝔭 := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toQ (L := L) 𝔭 (algebraMap ℂ (tens (κ' := κ') (placeAlg E)) a)).2
  refine
    { const_mem := hc
      isLocalRing := isLocalRing_locAt 𝔭 hinj
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc =
        (toQ (L := L) 𝔭).comp (algebraMap ℂ (tens (κ' := κ') (placeAlg E))) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toQ]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]

    letI : Algebra ℂ O' := ((algebraMap ℂ κ').codRestrict O' hO'.const_mem).toAlgebra
    haveI : IsScalarTower ℂ O' κ' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ O' := hO'.essFiniteType
    haveI : IsFractionRing O' κ' := IsFractionRing.of_field O' κ' fun f => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO'.frac f
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩
    haveI : Algebra.EssFiniteType O' κ' :=
      Algebra.EssFiniteType.of_isLocalization κ' (nonZeroDivisors O')
    haveI : Algebra.EssFiniteType ℂ κ' := Algebra.EssFiniteType.comp ℂ O' κ'

    haveI : Algebra.EssFiniteType ℂ (placeAlg E) := by
      let φ : E.ring →+* placeAlg E :=
        { toFun := fun x => ⟨x.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ : φ.FiniteType := RingHom.FiniteType.of_surjective φ fun y => ⟨⟨y.1, y.2⟩, rfl⟩
      have e : φ.comp ((algebraMap ℂ K).codRestrict E.ring E.const_mem) =
          algebraMap ℂ (placeAlg E) := RingHom.ext fun _ => rfl
      have h := RingHom.EssFiniteType.comp E.essFiniteType hφ.essFiniteType
      rw [e] at h
      exact RingHom.essFiniteType_algebraMap.1 h
    haveI : Algebra.EssFiniteType (placeAlg E) (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.baseChange ℂ κ' (placeAlg E)
    haveI : Algebra.EssFiniteType ℂ (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.comp ℂ (placeAlg E) (placeAlg E ⊗[ℂ] κ')
    haveI : Algebra.EssFiniteType ℂ (tens (κ' := κ') (placeAlg E)) :=
      Algebra.EssFiniteType.of_surjective (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom
        (tensEquiv (κ' := κ') (placeAlg E)).surjective
    have h1 : (algebraMap ℂ (tens (κ' := κ') (placeAlg E))).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 inferInstance

    letI : Algebra (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) := (toQ (L := L) 𝔭).toAlgebra
    haveI : IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) :=
      { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
        surj := fun x => by
          obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
          exact ⟨(a, ⟨s, hs⟩), hx⟩
        exists_of_eq := fun {x y} h => ⟨1, by
          simp only [OneMemClass.coe_one, one_mul]
          exact Subtype.ext (hinj (congrArg Subtype.val h))⟩ }
    haveI : Algebra.EssFiniteType (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) :=
      Algebra.EssFiniteType.of_isLocalization (locAt (L := L) 𝔭) 𝔭.primeCompl
    have h2 : (toQ (L := L) 𝔭).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hv0 : algebraMap (K ⊗[ℂ] κ') L v ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := exists_mul_mem_tens (κ' := κ') E u
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := exists_mul_mem_tens (κ' := κ') E v
    set D : K ⊗[ℂ] κ' := (d₁ * d₂) ⊗ₜ[ℂ] (1 : κ') with hD
    have hD1 : D = (d₂ ⊗ₜ[ℂ] (1 : κ')) * (d₁ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁]
    have hD2 : D = (d₁ ⊗ₜ[ℂ] (1 : κ')) * (d₂ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hu : D * u ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD1, mul_assoc]; exact mul_mem (tmul_mem hd₂ 1) h₁
    have hv' : D * v ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD2, mul_assoc]; exact mul_mem (tmul_mem hd₁ 1) h₂
    have hDu : IsUnit D := by
      refine IsUnit.of_mul_eq_one ((d₁ * d₂)⁻¹ ⊗ₜ[ℂ] (1 : κ')) ?_
      rw [hD, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (mul_ne_zero hd₁0 hd₂0)]
      rfl
    have hD0 : algebraMap (K ⊗[ℂ] κ') L D ≠ 0 := (hDu.map _).ne_zero
    refine ⟨_, (toQ (L := L) 𝔭 ⟨D * u, hu⟩).2, _, (toQ (L := L) 𝔭 ⟨D * v, hv'⟩).2, ?_, ?_⟩
    · show algebraMap (K ⊗[ℂ] κ') L (D * v) ≠ 0
      rw [map_mul]; exact mul_ne_zero hD0 hv0
    · show _ * algebraMap (K ⊗[ℂ] κ') L (D * v) = algebraMap (K ⊗[ℂ] κ') L (D * u)
      rw [map_mul, map_mul]
      field_simp

end GlobalTheory.GraphLocal
