import Mathlib
import GroundTheory.LocalFields.ArtinConductorIrreducible
import GroundTheory.LocalFields.ArtinConductorDiscriminant
import GroundTheory.LocalFields.BrauerInduction

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

open scoped Classical

section Dual

variable {G : Type*} [Group G]

theorem IsCharacter.comp_inv {χ : G → ℂ} (hχ : IsCharacter χ) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (σ : Representation ℂ G W), σ.character = fun g ↦ χ g⁻¹ := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  exact ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, ρ.dual,
    funext fun g ↦ char_dual ρ g⟩

end Dual

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Linear

theorem charArtinConductor_add (f g : (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (f + g) = charArtinConductor K L f + charArtinConductor K L g := by
  simp only [charArtinConductor, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem charArtinConductor_zsmul (n : ℤ) (f : (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (n • f) = n * charArtinConductor K L f := by
  simp only [charArtinConductor, Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  ring

theorem charArtinConductor_zero : charArtinConductor K L (0 : (L ≃ₐ[K] L) → ℂ) = 0 := by
  simp [charArtinConductor]

end Linear

variable [IsGalois K L]

theorem exists_nat_charArtinConductor_indLin (H : Subgroup (L ≃ₐ[K] L)) (l : H →* ℂˣ) :
    ∃ n : ℕ, charArtinConductor K L (indLin H l) = n := by
  set M := IntermediateField.fixedField H
  let e : H ≃* (L ≃ₐ[M] L) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H).symm).trans
      (IntermediateField.fixingSubgroupEquiv M)
  have hcomp : H.subtype.comp e.symm.toMonoidHom = AlgEquiv.restrictScalarsHom K := by
    ext σ x
    rfl
  obtain ⟨n, hn⟩ := exists_nat_charArtinConductor_inducedFun M (l.comp e.symm.toMonoidHom)
  refine ⟨n, ?_⟩
  rw [← hn, inducedFun_eq_indFun, ← hcomp, indLin]
  congr 1
  convert (indFun_comp_toMonoidHom H.subtype e.symm (fun h ↦ (l h : ℂ))).symm
  rfl

theorem exists_int_charArtinConductor_of_mem_spanZ {E : Subgroup (L ≃ₐ[K] L) → Prop}
    {f : (L ≃ₐ[K] L) → ℂ} (hf : f ∈ spanZ E) : ∃ k : ℤ, charArtinConductor K L f = k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, -, l, rfl⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_charArtinConductor_indLin H l
    exact ⟨n, by rw [hn]; push_cast; rfl⟩
  | zero => exact ⟨0, by rw [charArtinConductor_zero]; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [charArtinConductor_add, ha, hb]; push_cast; ring⟩
  | smul n x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨n * a, by rw [charArtinConductor_zsmul, ha]; push_cast; ring⟩

section Conditional

variable {E : Subgroup (L ≃ₐ[K] L) → Prop}

theorem exists_nat_artinConductor_of_mem_spanZ {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (L ≃ₐ[K] L) V) (h : ρ.character ∈ spanZ E) :
    ∃ n : ℕ, artinConductor ρ = n := by
  obtain ⟨k, hk⟩ := exists_int_charArtinConductor_of_mem_spanZ h
  have hq : artinConductor ρ = k := by
    apply Rat.cast_injective (α := ℂ)
    rw [artinConductor_eq_charArtinConductor, hk]
    push_cast
    rfl
  have hk0 : 0 ≤ k := by
    have := artinConductor_nonneg ρ
    rw [hq] at this
    exact_mod_cast this
  refine ⟨k.toNat, ?_⟩
  rw [hq]
  exact_mod_cast (Int.toNat_of_nonneg hk0).symm

omit [IsGalois K L] in

theorem isClassFun_artinCharacter : IsClassFun (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) := by
  intro σ τ
  simp only [artinCharacter_conj]

omit [IsGalois K L] in

theorem isClassFun_swanCharacter : IsClassFun (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) := by
  classical
  intro σ τ
  have h1 : τ * σ * τ⁻¹ = 1 ↔ σ = 1 := by
    constructor
    · intro h
      have := congrArg (fun x ↦ τ⁻¹ * x * τ) h
      simpa [mul_assoc] using this
    · rintro rfl
      simp
  have h0 : τ * σ * τ⁻¹ ∈ lowerRamificationGroup K L 0 ↔ σ ∈ lowerRamificationGroup K L 0 := by
    constructor
    · intro h
      have := (lowerRamificationGroup_normal K L 0).conj_mem _ h τ⁻¹
      simpa [mul_assoc] using this
    · intro h
      exact (lowerRamificationGroup_normal K L 0).conj_mem _ h τ
  simp only [swanCharacter, artinCharacter_conj]
  congr 3
  · exact if_congr h1 rfl rfl
  · exact if_congr h0 rfl rfl

omit [IsGalois K L] in

theorem charInner_artinCharacter (ψ : (L ≃ₐ[K] L) → ℂ) :
    charInner (L ≃ₐ[K] L) (fun σ ↦ (artinCharacter K L σ : ℂ)) ψ =
      charArtinConductor K L (fun σ ↦ ψ σ⁻¹) := by
  rw [charInner_apply, charArtinConductor]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _

omit [IsGalois K L] in

theorem charInner_swanCharacter (ψ : (L ≃ₐ[K] L) → ℂ) :
    charInner (L ≃ₐ[K] L) (fun σ ↦ (swanCharacter K L σ : ℂ)) ψ =
      charSwanConductor K L (fun σ ↦ ψ σ⁻¹) := by
  rw [charInner_apply, charSwanConductor]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _

theorem isCharacter_artinCharacter_of (hB : ∀ χ : (L ≃ₐ[K] L) → ℂ, IsCharacter χ → χ ∈ spanZ E) :
    IsCharacter (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) := by
  rw [isCharacter_iff]
  refine ⟨isClassFun_artinCharacter, fun ψ hψ ↦ ?_⟩
  obtain ⟨W, _, _, _, σ, hσ⟩ := (mem_irrChars.mp hψ).isCharacter.comp_inv
  obtain ⟨n, hn⟩ := exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))
  refine ⟨n, ?_⟩
  rw [charInner_artinCharacter, ← hσ, ← artinConductor_eq_charArtinConductor, hn]
  push_cast
  rfl

theorem isCharacter_swanCharacter_of (hB : ∀ χ : (L ≃ₐ[K] L) → ℂ, IsCharacter χ → χ ∈ spanZ E) :
    IsCharacter (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) := by
  rw [isCharacter_iff]
  refine ⟨isClassFun_swanCharacter, fun ψ hψ ↦ ?_⟩
  obtain ⟨W, _, _, _, σ, hσ⟩ := (mem_irrChars.mp hψ).isCharacter.comp_inv
  obtain ⟨n, hn⟩ := exists_nat_artinConductor_of_mem_spanZ σ (hB _ (isCharacter_character σ))
  obtain ⟨k, hk⟩ := exists_nat_swanConductor_eq_of_artinConductor_eq σ hn
  refine ⟨k, ?_⟩
  rw [charInner_swanCharacter, ← hσ, ← swanConductor_eq_charSwanConductor, hk]
  push_cast
  rfl

end Conditional

section Final

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in

theorem IsCharacter.mem_spanZ_isElementary {χ : (L ≃ₐ[K] L) → ℂ} (hχ : IsCharacter χ) :
    χ ∈ spanZ (IsElementary (G := L ≃ₐ[K] L)) :=
  mem_spanZ_of_mono (fun _ hK _ hψ ↦ hK.exists_eq_indLin hψ) hχ

theorem exists_nat_artinConductor {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ∃ n : ℕ, artinConductor ρ = n :=
  exists_nat_artinConductor_of_mem_spanZ ρ (isCharacter_character ρ).mem_spanZ_isElementary

theorem exists_nat_charArtinConductor {χ : (L ≃ₐ[K] L) → ℂ} (hχ : IsCharacter χ) :
    ∃ n : ℕ, charArtinConductor K L χ = n := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := hχ
  obtain ⟨n, hn⟩ := exists_nat_artinConductor ρ
  exact ⟨n, by rw [← artinConductor_eq_charArtinConductor, hn]; push_cast; rfl⟩

theorem exists_nat_swanConductor {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) : ∃ k : ℕ, swanConductor ρ = k :=
  let ⟨_, hn⟩ := exists_nat_artinConductor ρ
  exists_nat_swanConductor_eq_of_artinConductor_eq ρ hn

theorem isCharacter_artinCharacter : IsCharacter (fun σ : L ≃ₐ[K] L ↦ (artinCharacter K L σ : ℂ)) :=
  isCharacter_artinCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary

theorem isCharacter_swanCharacter : IsCharacter (fun σ : L ≃ₐ[K] L ↦ (swanCharacter K L σ : ℂ)) :=
  isCharacter_swanCharacter_of fun _ hχ ↦ hχ.mem_spanZ_isElementary

theorem addVal_discr_eq_sum_irrChars_nat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    ∃ f d : ((L ≃ₐ[K] L) → ℂ) → ℕ, (∀ χ ∈ irrChars (L ≃ₐ[K] L),
      charArtinConductor K L χ = f χ ∧ χ 1 = d χ) ∧
      IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) =
        ((∑ χ ∈ irrChars (L ≃ₐ[K] L), d χ * f χ : ℕ) : ℕ∞) := by
  have hf : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, charArtinConductor K L χ = n := fun χ hχ ↦
    exists_nat_charArtinConductor (mem_irrChars.mp hχ).isCharacter
  have hd : ∀ χ ∈ irrChars (L ≃ₐ[K] L), ∃ n : ℕ, χ 1 = n := fun χ hχ ↦
    let ⟨n, _, hn⟩ := (mem_irrChars.mp hχ).exists_one
    ⟨n, hn⟩
  choose! f hf using hf
  choose! d hd using hd
  obtain ⟨n, hn, hsum⟩ := addVal_discr_eq_sum_irrChars (K := K) (L := L) b
  refine ⟨f, d, fun χ hχ ↦ ⟨hf χ hχ, hd χ hχ⟩, ?_⟩
  rw [hn]
  congr 1
  apply Nat.cast_injective (R := ℂ)
  rw [hsum]
  push_cast
  exact Finset.sum_congr rfl fun χ hχ ↦ by rw [hf χ hχ, hd χ hχ]

theorem span_discr_eq_prod_irrChars {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    ∃ f d : ((L ≃ₐ[K] L) → ℂ) → ℕ, (∀ χ ∈ irrChars (L ≃ₐ[K] L),
      charArtinConductor K L χ = f χ ∧ χ 1 = d χ) ∧
      Ideal.span {Algebra.discr 𝒪[K] b} =
        ∏ χ ∈ irrChars (L ≃ₐ[K] L), (IsLocalRing.maximalIdeal 𝒪[K] ^ f χ) ^ d χ := by
  obtain ⟨f, d, hfd, hval⟩ := addVal_discr_eq_sum_irrChars_nat b
  refine ⟨f, d, hfd, ?_⟩
  have hne : Algebra.discr 𝒪[K] b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hval
    exact ENat.top_ne_natCast _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hm : m = ∑ χ ∈ irrChars (L ≃ₐ[K] L), d χ * f χ := by
    have := IsDiscreteValuationRing.addVal_def _ u hϖ m hu
    rw [hval] at this
    exact_mod_cast this.symm
  rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq, hm]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_congr rfl fun χ _ ↦ mul_comm _ _

end Final

end GroundTheory.LocalField
