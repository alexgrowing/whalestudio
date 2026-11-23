import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Formalism.LocalToGlobal.Divisibility.Tuples

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

variable (L : Type) [Field L] [NumberField L]

def simTA (c : L →ₐ[ℚ] L) : Subgroup (AfE ℚ L)ˣ where
  carrier := {x | ∃ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, x * conjId c x = idF ℚ L t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    rw [map_mul, map_mul, ← hs, ← ht]
    exact mul_mul_mul_comm x y (conjId c x) (conjId c y)
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv, map_inv, ← hs, mul_inv]

def ratT (c : L →ₐ[ℚ] L) : Subgroup (simTA L c) :=
  ((simT ℚ c).map (ratId ℚ L)).subgroupOf (simTA L c)

theorem ratId_mem_simTA (c : L →ₐ[ℚ] L) {a : Lˣ} (ha : a ∈ simT ℚ c) : ratId ℚ L a ∈ simTA L c := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom t, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, ratId, conjId, idF, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Algebra.TensorProduct.includeRight_apply]
  rw [ht, Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem conjId_ratId (c : L →ₐ[ℚ] L) (a : Lˣ) :
    conjId c (ratId ℚ L a) = ratId ℚ L (Units.map (c : L →+* L).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem idF_map_algebraMap (r : ℚˣ) :
    idF ℚ L (Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r) =
      ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r) := by
  apply Units.ext
  simp only [idF, ratId, inclE, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_coe,
    AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem sigR_mem_RInt (c : L →ₐ[ℚ] L) {y : AfE ℚ L} (hy : y ∈ RInt ℚ L) :
    sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ RInt ℚ L := by
  have hle : RInt ℚ L ≤ (RInt ℚ L).comap (sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨d, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨c (algebraMap (𝓞 L) L b), ⟨RingOfIntegers.mapRingHom (c : L →+* L) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨d, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (c : L →ₐ[ℚ] L) {k : (AfE ℚ L)ˣ} (hk : k ∈ intU ℚ L) : conjId c k ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt L c hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt L c hk.2

theorem idF_mem_intU {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hu : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ)
    (hu' : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ) : idF ℚ L u ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff]
  refine ⟨Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩), ?_⟩
  rw [← map_inv]
  exact Subring.subset_closure (Or.inr ⟨⟨_, hu'⟩, rfl⟩)

end GlobalTheory.LKTorus
