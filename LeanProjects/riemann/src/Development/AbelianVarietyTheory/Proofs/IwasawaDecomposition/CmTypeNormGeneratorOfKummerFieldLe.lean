import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiGen

open GlobalTheory.Mem.FieldsEx GlobalTheory.Mem.BaseExt GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

variable {E : Type} [Field E] [NumberField E]

theorem typeNorm_of_root [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (𝔞 : Ideal (𝓞 E)) {h : ℕ} (hpos : 0 < h) (γ : 𝓞 E) (h0 : γ ≠ 0)
    (hγ : 𝔞 ^ h = Ideal.span {γ}) (β : K) (hb : (β : ℂ) ^ h = ∏ τ : E →+* ℂ, τ (γ : E) ^ r τ) : β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  have hβ : β ^ h = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ h)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

theorem exists_gen_basis (b : ClassBasis E) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (γ : 𝓞 E) (α : Eˣ) (a : Fin b.k → ℤ) (k : Fin b.k → ℕ), γ ≠ 0 ∧ (∀ i, classNumber E = b.h i * k i) ∧
      𝔞 ^ classNumber E = Ideal.span {γ} ∧
      (γ : E) = ((α ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i : Eˣ) : E) := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠))
  have hk : ∀ i, ∃ k, classNumber E = b.h i * k := fun i => (orderOf_dvd_card : b.h i ∣ classNumber E)
  choose k hk using hk
  have h1 : ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠 * (∏ i, b.c i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, mul_inv_cancel]
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx
    exact Units.ne_zero _ hx
  have h2 : FractionalIdeal.mk0 E 𝔠 = toPrincipalIdeal (𝓞 E) E (Units.mk0 x hx0) * ∏ i, b.c i ^ a i := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact Units.ext (by rw [hx, coe_toPrincipalIdeal]; rfl)
  set y : Eˣ := Units.mk0 x hx0 ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i with hy
  have h3 : FractionalIdeal.mk0 E 𝔠 ^ classNumber E = toPrincipalIdeal (𝓞 E) E y := by
    rw [h2, hy, mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_pow, ← b.pow_eq i, ← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm, hk i]
    rfl
  have h4 : ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) := by
    rw [← coe_toPrincipalIdeal, ← h3, FractionalIdeal.coeIdeal_pow, Units.val_pow_eq_pow_val]
    rfl
  have h5 : (y : E) ∈ ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [h4]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨γ, -, hγ⟩ := (FractionalIdeal.mem_coeIdeal _).1 h5
  refine ⟨γ, Units.mk0 x hx0, a, k, ?_, hk, ?_, hγ⟩
  · rintro rfl
    exact y.ne_zero (by rw [← hγ, map_zero])
  · apply FractionalIdeal.coeIdeal_injective (K := E)
    simp only
    rw [h4, FractionalIdeal.coeIdeal_span_singleton, hγ]

theorem typeNorm_of_basis [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (b : ClassBasis E)
    (hb : ∀ i (z : ℂ), z ^ b.h i = ∏ τ : E →+* ℂ, τ (b.γ i : E) ^ r τ → z ∈ K)
    (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  obtain ⟨γ, α, a, k, h0, hk, hγ, hy⟩ := exists_gen_basis b 𝔞 h𝔞
  let Ψ : Eˣ →* ℂ :=
    { toFun := fun x => ∏ τ : E →+* ℂ, τ (x : E) ^ r τ
      map_one' := by simp
      map_mul' := fun x y => by simp only [Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib] }
  choose ψ hψ using fun i => IsAlgClosed.exists_pow_nat_eq (Ψ (b.γ i)) (b.h_pos i)
  have hm : Ψ α * ∏ i, ψ i ^ a i ∈ K :=
    mul_mem (prod_mem fun τ _ => pow_mem (hK τ _) _) (prod_mem fun i _ => zpow_mem (hb i _ (hψ i)) _)
  refine ⟨⟨_, hm⟩, typeNorm_of_root r n hr K hK 𝔞 (classNumber_pos E) γ h0 hγ _ ?_⟩
  rw [hy]
  change (Ψ α * ∏ i, ψ i ^ a i) ^ _ = Ψ _
  rw [mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, map_pow, ← hψ i, ← pow_mul, ← hk i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem typeNorm_gen_of_kPsi_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  intro P δ F _ j hF 𝔞 h𝔞
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  simp only [FieldDat.KPsi, kPsiField, sup_le_iff, imField_le_iff, IntermediateField.adjoin_le_iff] at hF
  obtain ⟨⟨hE, -⟩, hψ⟩ := hF
  have hK : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F := fun τ x => by
    obtain ⟨σ, hσ⟩ := exists_aut P.host.φ₀ τ
    rw [hσ]; exact hE _
  obtain ⟨β, hβ, hsp, hn⟩ := typeNorm_of_basis (typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2) _
    (typeExp_add P.host _ _) F hK δ.basis (fun i z hz => hψ ⟨i, by
      rw [hz, prod_typeExp, typeNorm, map_prod]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [map_mul, map_pow, map_pow, conjugate_emb_apply]
      rfl⟩) 𝔞 h𝔞
  refine ⟨β, hβ, ?_, hn⟩
  rw [hsp, prod_typeExp]
  refine Finset.prod_congr rfl fun g _ => ?_
  simp only [conjugate_emb_apply]
  rfl

end GlobalTheory.Mem.KPsiGen

end
