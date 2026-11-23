import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
open scoped WithZero

namespace GlobalTheory.TamOne

section Residue

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tmul_algebraMap_mul_eq {F E' A : Type} [Field F] [Field E'] [Algebra F E'] [CommRing A] [Algebra F A]
    (c : F) (a : A) (y : E') : a ⊗ₜ[F] (algebraMap F E' c * y) = (algebraMap F A c * a) ⊗ₜ[F] y := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

theorem coe_algebraMap_ringOfIntegers (t : 𝓞 (maximalRealSubfield E)) :
    ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t : 𝓞 E) : E) =
      algebraMap (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) t) := by
  first
  | rfl
  | exact (IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E t).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E t)

theorem mem_extIdeal_of_intLocIncl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (x : 𝓞 E)
    (hx : intLocIncl v x ∈ (extIdeal v).map (intLocIncl v)) : x ∈ extIdeal v := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπv : v.valuation (maximalRealSubfield E)
      (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π) = WithZero.exp (-1) :=
    (v.valuation_of_algebraMap (K := maximalRealSubfield E) π).trans hπ
  let S : Ideal (intLoc (maximalRealSubfield E) E v) :=
    { carrier := {z | (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π)⁻¹ •
          (z : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) ∈ intLoc (maximalRealSubfield E) E v}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddMemClass.coe_add, smul_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c z hz => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul] at hz ⊢
        rw [← mul_smul_comm]
        exact mul_mem c.2 hz }
  have hval : ∀ c : maximalRealSubfield E, Valued.v (algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v) c) =
      v.valuation (maximalRealSubfield E) c := fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c
  have hIS : (extIdeal v).map (intLocIncl v) ≤ S := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro t ht
    change (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π)⁻¹ •
      ((intLocIncl v (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t) : intLoc (maximalRealSubfield E) E v) :
        Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) ∈ intLoc (maximalRealSubfield E) E v
    rw [coe_intLocIncl, coe_algebraMap_ringOfIntegers, ← mul_one (algebraMap (maximalRealSubfield E) E _),
      tmul_algebraMap_mul_eq, TensorProduct.smul_tmul']
    have h1 : v.valuation (maximalRealSubfield E) (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) t) ≤
        WithZero.exp (-1) := by
      refine (v.valuation_of_algebraMap (K := maximalRealSubfield E) t).trans_le ?_
      have := (v.intValuation_le_pow_iff_mem t 1).2 (by rwa [pow_one])
      simpa using this
    have hmem : (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π)⁻¹ •
        (algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v)
          (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) t) * 1) ∈
        v.adicCompletionIntegers (maximalRealSubfield E) := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, mul_one, ← map_mul,
        hval, map_mul, map_inv₀, hπv]
      calc (WithZero.exp (-1))⁻¹ * v.valuation (maximalRealSubfield E)
              (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) t)
          ≤ (WithZero.exp (-1))⁻¹ * WithZero.exp (-1) := by gcongr
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    exact tmul_mem_intLoc (E := E) hmem (1 : 𝓞 E)
  have hxS := hIS hx
  change (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π)⁻¹ •
    ((intLocIncl v x : intLoc (maximalRealSubfield E) E v) :
      Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) ∈ intLoc (maximalRealSubfield E) E v at hxS
  rw [coe_intLocIncl, ← TensorProduct.tmul_smul] at hxS
  obtain ⟨k, s, φ, hφ, hsum⟩ :=
    GlobalTheory.AdelicU.SelfDual.exists_dualFamily_integers (F := maximalRealSubfield E) (E := E)
  have hr : ∀ j, ∃ r : 𝓞 (maximalRealSubfield E), r ∈ v.asIdeal ∧
      φ j (x : E) = algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r := by
    intro j
    obtain ⟨r, hr⟩ := hφ x j
    refine ⟨r, ?_, hr.symm⟩
    have h1 := GlobalTheory.AdelicU.SelfDual.valuation_le_one_of_intLoc (v := v) (φ j) (hφ · j)
      (e := (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π)⁻¹ • (x : E)) hxS
    rw [map_smul, smul_eq_mul, map_mul, map_inv₀, hπv, ← hr] at h1
    rw [← v.valuation_lt_one_iff_mem (K := maximalRealSubfield E)]
    have h2 : v.valuation (maximalRealSubfield E) (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r) ≤
        WithZero.exp (-1) := by
      calc _ = WithZero.exp (-1) * ((WithZero.exp (-1))⁻¹ *
              v.valuation (maximalRealSubfield E) (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r)) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp (-1) * 1 := by gcongr
        _ = _ := mul_one _
    exact h2.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  choose r hrv hr using hr
  have hx' : x = ∑ j, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (r j) * s j := by
    apply RingOfIntegers.ext
    conv_lhs => rw [← hsum (x : E)]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hr j, Algebra.smul_def]
    congr 1
  rw [hx']
  exact sum_mem fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hrv j))

theorem exists_sub_intLocIncl_mem_map (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (z : intLoc (maximalRealSubfield E) E v) :
    ∃ x : 𝓞 E, z - intLocIncl v x ∈ (extIdeal v).map (intLocIncl v) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπv : v.valuation (maximalRealSubfield E)
      (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π) = WithZero.exp (-1) :=
    (v.valuation_of_algebraMap (K := maximalRealSubfield E) π).trans hπ
  have hπI : π ∈ v.asIdeal := by
    have := (v.intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  suffices H : ∀ y ∈ intLoc (maximalRealSubfield E) E v, ∃ x : 𝓞 E,
      ∃ w ∈ (extIdeal v).map (intLocIncl v),
        y = (intLocIncl v x : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) +
          (w : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) by
    obtain ⟨x, w, hw, h⟩ := H z z.2
    refine ⟨x, ?_⟩
    have : z - intLocIncl v x = w := Subtype.ext (by simp [h])
    rw [this]
    exact hw
  intro y hy
  refine intLoc_induction (p := fun y => ∃ x : 𝓞 E, ∃ w ∈ (extIdeal v).map (intLocIncl v),
      y = (intLocIncl v x : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) +
        (w : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) ?_ ?_ ?_ ?_ hy
  · intro a ha y'
    obtain ⟨s, hs⟩ := GlobalTheory.Idele.exists_valued_sub_le (R := 𝓞 (maximalRealSubfield E)) (K := maximalRealSubfield E) v
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha) 1
    have hval : ∀ c : maximalRealSubfield E, Valued.v (algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v) c) =
        v.valuation (maximalRealSubfield E) c := fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c
    have hπ0 : algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v)
        (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π) ≠ 0 := by
      intro h
      have := congrArg Valued.v h
      rw [hval, hπv, map_zero] at this
      exact WithZero.exp_ne_zero this
    set b := (a - algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v)
      (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) s)) *
        (algebraMap (maximalRealSubfield E) (Fv (maximalRealSubfield E) v)
          (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π))⁻¹ with hb_def
    have hb : b ∈ v.adicCompletionIntegers (maximalRealSubfield E) := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hb_def, map_mul, map_inv₀, hval, hπv]
      calc _ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) * (WithZero.exp (-1))⁻¹ := by gcongr
        _ = 1 := by rw [Nat.cast_one]; exact mul_inv_cancel₀ WithZero.exp_ne_zero
    refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s * y',
      intLocIncl v (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) π) * ⟨b ⊗ₜ[maximalRealSubfield E] (y' : E),
        tmul_mem_intLoc hb y'⟩,
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hπI)), ?_⟩
    rw [Subring.coe_mul, coe_intLocIncl, coe_intLocIncl, Algebra.TensorProduct.tmul_mul_tmul]
    show a ⊗ₜ[maximalRealSubfield E] (y' : E) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] (algebraMap (maximalRealSubfield E) E
        (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) s) * (y' : E)) +
      (1 * b) ⊗ₜ[maximalRealSubfield E] (algebraMap (maximalRealSubfield E) E
        (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) π) * (y' : E))
    rw [tmul_algebraMap_mul_eq,
      tmul_algebraMap_mul_eq, ← TensorProduct.add_tmul]
    congr 1
    rw [hb_def]
    field_simp
    ring
  · exact ⟨0, 0, zero_mem _, by simp⟩
  · rintro _ _ ⟨x, w, hw, rfl⟩ ⟨x', w', hw', rfl⟩
    exact ⟨x + x', w + w', add_mem hw hw', by simp only [map_add, Subring.coe_add]; abel⟩
  · rintro _ ⟨x, w, hw, rfl⟩
    exact ⟨-x, -w, neg_mem hw, by simp only [map_neg, Subring.coe_neg]; abel⟩

end Residue

theorem exists_residueMap_intLoc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ ρ : intLoc (maximalRealSubfield E) E v →+* 𝓞 E ⧸ extIdeal v,
      Function.Surjective ρ ∧ (∀ x, ρ (intLocIncl v x) = Ideal.Quotient.mk (extIdeal v) x) ∧
        ∀ z, ρ z = 0 ↔ z ∈ (extIdeal v).map (intLocIncl v) := by
  intro E _ _ _ _ v
  have H : extIdeal v ≤ ((extIdeal v).map (intLocIncl v)).comap (intLocIncl v) := Ideal.le_comap_map
  have hinj : Function.Injective (Ideal.quotientMap ((extIdeal v).map (intLocIncl v)) (intLocIncl v) H) :=
    Ideal.quotientMap_injective' fun x hx => mem_extIdeal_of_intLocIncl_mem v x hx
  have hsurj : Function.Surjective (Ideal.quotientMap ((extIdeal v).map (intLocIncl v)) (intLocIncl v) H) := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨x, hx⟩ := exists_sub_intLocIncl_mem_map v z
    exact ⟨Ideal.Quotient.mk _ x, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hx).symm⟩
  obtain ⟨e, he⟩ : ∃ e : 𝓞 E ⧸ extIdeal v ≃+* intLoc (maximalRealSubfield E) E v ⧸ (extIdeal v).map (intLocIncl v),
      ∀ q, e q = Ideal.quotientMap ((extIdeal v).map (intLocIncl v)) (intLocIncl v) H q :=
    ⟨RingEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun _ => rfl⟩
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk ((extIdeal v).map (intLocIncl v))), ?_, fun x => ?_, fun z => ?_⟩
  · intro q
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (e q)
    exact ⟨z, by simp only [RingHom.comp_apply, hz]; exact e.symm_apply_apply q⟩
  · show e.symm (Ideal.Quotient.mk _ (intLocIncl v x)) = _
    exact e.symm_apply_eq.2 ((he _).trans Ideal.quotientMap_mk).symm
  · show e.symm (Ideal.Quotient.mk _ z) = 0 ↔ _
    exact (map_eq_zero_iff _ e.symm.injective).trans Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory.TamOne
