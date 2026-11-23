import Mathlib
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff

noncomputable section

open IsDedekindDomain NumberField
open scoped Pointwise

namespace GroundTheory.Global

section Average

variable {G H : Type*} [Group G] [Group H]

theorem card_mul_sum_comp_of_surjective {A B : Type*} [Group A] [Group B] [Fintype A]
    [Fintype B] (ψ : A →* B) (hψ : Function.Surjective ψ) (F : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, F (ψ a) = (Fintype.card A : ℂ) * ∑ b, F b := by
  have h1 : ∀ b : B, ∑ a, F (b * ψ a) = ∑ a, F (ψ a) := by
    intro b
    obtain ⟨a₀, rfl⟩ := hψ b
    calc ∑ a, F (ψ a₀ * ψ a) = ∑ a, F (ψ (a₀ * a)) := by simp only [map_mul]
      _ = ∑ a, F (ψ a) := Equiv.sum_comp (Equiv.mulLeft a₀) (fun a => F (ψ a))
  have h2 : ∀ a : A, ∑ b, F (b * ψ a) = ∑ b, F b := fun a =>
    Equiv.sum_comp (Equiv.mulRight (ψ a)) F
  calc (Fintype.card B : ℂ) * ∑ a, F (ψ a) = ∑ _b : B, ∑ a, F (ψ a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ b : B, ∑ a, F (b * ψ a) := Finset.sum_congr rfl fun b _ => (h1 b).symm
    _ = ∑ a : A, ∑ b, F (b * ψ a) := Finset.sum_comm
    _ = ∑ _a : A, ∑ b, F b := Finset.sum_congr rfl fun a _ => h2 a
    _ = (Fintype.card A : ℂ) * ∑ b, F b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem cosetAverage_comp (I : Subgroup G) [Finite I] (π : G →* H) (f : H → ℂ) (g : G) :
    cosetAverage I (f ∘ π) g = cosetAverage (I.map π) f (π g) := by
  classical
  have : Finite (I.map π) := Finite.of_surjective _ (π.subgroupMap_surjective I)
  have : Fintype I := Fintype.ofFinite _
  have : Fintype (I.map π) := Fintype.ofFinite _
  have key := card_mul_sum_comp_of_surjective (π.subgroupMap I) (π.subgroupMap_surjective I)
    (fun j => f (π g * j))
  have hI : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJ : (Fintype.card (I.map π) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold cosetAverage
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff hI hJ]
  simp only [Function.comp_apply, map_mul]
  have hsub : ∀ i : I, π (i : G) = ((π.subgroupMap I i : I.map π) : H) := fun _ => rfl
  simp only [hsub]
  linear_combination key

end Average

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem algebraMap_restrictNormalHom_smul (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap F L ((σ.restrictNormal F) (x : F)) = σ (algebraMap F L (x : F))
  exact AlgEquiv.restrictNormal_commutes σ F x

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem under_smul (σ : Gal(L/K)) (Q : Ideal (𝓞 L)) :
    (σ • Q).under (𝓞 F) = AlgEquiv.restrictNormalHom F σ • Q.under (𝓞 F) := by
  ext x
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.under_def, Ideal.mem_comap,
    ← map_inv, algebraMap_restrictNormalHom_smul]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_restrictScalars (g : Gal(L/F)) :
    AlgEquiv.restrictNormalHom F (g.restrictScalars K) = 1 := by
  refine AlgEquiv.ext fun x => (algebraMap F L).injective ?_
  change algebraMap F L (((g.restrictScalars K).restrictNormal F) x) = algebraMap F L x
  rw [AlgEquiv.restrictNormal_commutes]
  exact g.commutes x

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K F] [IsGalois K L] in

theorem restrictScalars_smul_ideal (g : Gal(L/F)) (I : Ideal (𝓞 L)) :
    g.restrictScalars K • I = g • I := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  rfl

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_mem_stabilizer {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) Q) :
    AlgEquiv.restrictNormalHom F σ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [← under_smul, hσ]

omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L] in

theorem restrictNormalHom_mem_inertia {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Q.inertia Gal(L/K)) :
    AlgEquiv.restrictNormalHom F σ ∈ (Q.under (𝓞 F)).inertia Gal(F/K) := by
  rw [AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x - x) ∈ Q
  rw [map_sub, algebraMap_restrictNormalHom_smul]
  exact hσ _

omit [NumberField K] in

theorem exists_mem_stabilizer_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F))) :
    ∃ σ ∈ MulAction.stabilizer Gal(L/K) Q, AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₀, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) L τ
  have : (σ₀ • Q).LiesOver (Q.under (𝓞 F)) :=
    ⟨by rw [under_smul, MulAction.mem_stabilizer_iff.1 hτ]⟩
  obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Q.under (𝓞 F)) (σ₀ • Q) Q Gal(L/F)
  refine ⟨g.restrictScalars K * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, restrictScalars_smul_ideal, hg]
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul]

theorem exists_mem_inertia_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ (Q.under (𝓞 F)).inertia Gal(F/K)) :
    ∃ σ ∈ Q.inertia Gal(L/K), AlgEquiv.restrictNormalHom F σ = τ := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  obtain ⟨σ₁, hσ₁Q, hσ₁⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q
    (Ideal.inertia_le_stabilizer _ hτ)

  let e₀ := Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) Gal(L/K) ⟨σ₁, hσ₁Q⟩
  have he₀ : ∀ y : 𝓞 L, e₀ (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl

  let e : (𝓞 L ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      change e₀ (Ideal.Quotient.mk Q (algebraMap (𝓞 F) (𝓞 L) x)) = _
      rw [he₀, ← algebraMap_restrictNormalHom_smul, Ideal.Quotient.eq, ← map_sub, hσ₁]
      exact AddSubgroup.mem_inertia.1 hτ x)
  have he : ∀ y : 𝓞 L, e (Ideal.Quotient.mk Q y) = Ideal.Quotient.mk Q (σ₁ • y) :=
    fun _ => rfl
  obtain ⟨ρ, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(L/F) (Q.under (𝓞 F)) Q e.symm
  have hρ' : ∀ z : 𝓞 L,
      Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • z) = e.symm (Ideal.Quotient.mk Q z) :=
    fun z => by rw [← hρ]; rfl
  refine ⟨(ρ : Gal(L/F)).restrictScalars K * σ₁, ?_, ?_⟩
  · rw [AddSubgroup.mem_inertia]
    intro y
    change _ ∈ Q
    rw [← Ideal.Quotient.eq]
    calc Ideal.Quotient.mk Q (((ρ : Gal(L/F)).restrictScalars K * σ₁) • y)
        = Ideal.Quotient.mk Q ((ρ : Gal(L/F)) • (σ₁ • y)) := by rw [mul_smul]; rfl
      _ = e.symm (e (Ideal.Quotient.mk Q y)) := by rw [hρ', he]
      _ = Ideal.Quotient.mk Q y := e.symm_apply_apply _
  · rw [map_mul, restrictNormalHom_restrictScalars, one_mul, hσ₁]

omit [NumberField K] in

theorem map_stabilizer_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (MulAction.stabilizer Gal(L/K) Q).map (AlgEquiv.restrictNormalHom F) =
      MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_stabilizer hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_stabilizer_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩

theorem map_inertia_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom F) =
      (Q.under (𝓞 F)).inertia Gal(F/K) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact restrictNormalHom_mem_inertia hσ
  · intro hτ
    obtain ⟨σ, hσ, h⟩ := exists_mem_inertia_restrictNormalHom_eq Q hτ
    exact ⟨σ, hσ, h⟩

theorem IsArithFrobAt.restrictNormalHom {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by
  intro x
  rw [Ideal.under_under]
  change algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F φ • x -
    x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K))) ∈ Q
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact h _

end GroundTheory.Global
