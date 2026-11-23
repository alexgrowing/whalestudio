import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycBasic

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section Tower

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]

omit [IsScalarTower ℚ E L] in
theorem res_smul (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L) (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (x : 𝓞 E) :
    algebraMap (𝓞 E) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 E) (𝓞 L) x := by
  apply RingOfIntegers.coe_injective
  exact h x

omit [IsScalarTower ℚ E L] [NumberField E] [NumberField L] in
theorem mem_over_iff (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] (x : 𝓞 E) :
    x ∈ P ↔ algebraMap (𝓞 E) (𝓞 L) x ∈ Q := by
  rw [Ideal.over_def Q P, Ideal.under_def, Ideal.mem_comap]

omit [IsScalarTower ℚ E L] in
theorem inertia_res (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (hτ : ∀ y : 𝓞 L, τ • y - y ∈ Q) (x : 𝓞 E) :
    σ • x - x ∈ P := by
  rw [mem_over_iff P Q, map_sub, res_smul σ τ h]
  exact hτ _

omit [IsScalarTower ℚ E L] in
theorem frob_res (p : ℕ) (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.LiesOver P] [Q.LiesOver (span {(p : ℤ)})]
    [P.LiesOver (span {(p : ℤ)})] (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L)
    (h : ∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ σ P := by
  intro x
  have hx : τ • algebraMap (𝓞 E) (𝓞 L) x - algebraMap (𝓞 E) (𝓞 L) x ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q :=
    hτ (algebraMap (𝓞 E) (𝓞 L) x)
  show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
  rw [odd_card_under p Q] at hx
  rw [odd_card_under p P, mem_over_iff P Q, map_sub, map_pow, res_smul σ τ h]
  exact hx

theorem smul_mem_of_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (I : Ideal S)
    (h : ∀ x : S, g • x - x ∈ I) (z : S) : g • z ∈ I ↔ z ∈ I :=
  ⟨fun hz => by simpa using I.sub_mem hz (h z), fun hz => by simpa using I.add_mem (h z) hz⟩

theorem inertia_lift [IsGalois ℚ L] (P : Ideal (𝓞 E)) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P] (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ x : 𝓞 E, σ • x - x ∈ P) :
    ∃ τ : L ≃ₐ[ℚ] L, (∀ x, algebraMap E L (σ x) = τ (algebraMap E L x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q := by
  have : IsGalois E L := IsGalois.tower_top_of_isGalois ℚ E L
  have hinv : Algebra.IsInvariant (𝓞 E) (𝓞 L) (L ≃ₐ[E] L) := inferInstance
  let τ₀ : L ≃ₐ[ℚ] L := σ.liftNormal L
  have h₀ : ∀ x, algebraMap E L (σ x) = τ₀ (algebraMap E L x) := fun x => (AlgEquiv.liftNormal_commutes σ L x).symm
  have hunder : (τ₀⁻¹ • Q).under (𝓞 E) = Q.under (𝓞 E) := by
    ext a
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff,
      ← res_smul σ τ₀ h₀, ← mem_over_iff P Q, ← mem_over_iff P Q]
    exact smul_mem_of_inertia σ P hσ a
  obtain ⟨ρ, hρ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 E) (𝓞 L) (L ≃ₐ[E] L) Q (τ₀⁻¹ • Q) hunder.symm
  let τ₁ : L ≃ₐ[ℚ] L := τ₀ * ρ.restrictScalars ℚ
  have hs : ∀ (r : L ≃ₐ[E] L) (y : 𝓞 L), (r.restrictScalars ℚ) • y = r • y := fun _ _ => rfl
  have h₁ : ∀ x, algebraMap E L (σ x) = τ₁ (algebraMap E L x) := fun x => by
    show _ = τ₀ (ρ (algebraMap E L x))
    rw [ρ.commutes, h₀]
  have hst : τ₁ ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q := by
    refine Decomp.mem_stab_of τ₁ Q fun z => ?_
    rw [mul_smul, hs, ← Ideal.mem_inv_pointwise_smul_iff, hρ]
    exact Ideal.smul_mem_pointwise_smul_iff
  let f : (𝓞 L ⧸ Q) ≃ₐ[𝓞 E ⧸ P] (𝓞 L ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (Ideal.Quotient.stabilizerHom Q (Q.under ℤ) (L ≃ₐ[ℚ] L) ⟨τ₁, hst⟩).toRingEquiv) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show Ideal.Quotient.mk Q (τ₁ • algebraMap (𝓞 E) (𝓞 L) a) = Ideal.Quotient.mk Q (algebraMap (𝓞 E) (𝓞 L) a)
      rw [Ideal.Quotient.eq, ← res_smul σ τ₁ h₁, ← map_sub, ← mem_over_iff P Q]
      exact hσ a)
  obtain ⟨r, hr⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[E] L) P Q f
  refine ⟨τ₁ * (r.1⁻¹).restrictScalars ℚ, fun x => ?_, fun y => ?_⟩
  · show _ = τ₁ ((r.1⁻¹) (algebraMap E L x))
    rw [AlgEquiv.commutes, h₁]
  · have h2 : Ideal.Quotient.mk Q (r.1 • (r.1⁻¹ • y)) = Ideal.Quotient.mk Q (τ₁ • (r.1⁻¹ • y)) :=
      DFunLike.congr_fun hr (Ideal.Quotient.mk Q (r.1⁻¹ • y))
    rw [smul_inv_smul] at h2
    rw [mul_smul, hs, ← Ideal.Quotient.eq]
    exact h2.symm

end Tower

theorem exists_over {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [IsGalois ℚ L] (ι : E →ₐ[ℚ] L)
    (l : ℕ) (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (span {(l : ℤ)})),
      (∀ (σ : E ≃ₐ[ℚ] E), (∀ x : 𝓞 E, σ • x - x ∈ P) ↔
        ∃ τ : L ≃ₐ[ℚ] L, (∀ x, ι (σ x) = τ (ι x)) ∧ ∀ y : 𝓞 L, τ • y - y ∈ Q) ∧
      ∀ (σ : E ≃ₐ[ℚ] E) (τ : L ≃ₐ[ℚ] L), (∀ x, ι (σ x) = τ (ι x)) → IsArithFrobAt ℤ τ Q → IsArithFrobAt ℤ σ P := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  obtain ⟨⟨Q, hQp, hQl⟩⟩ : Nonempty (P.primesOver (𝓞 L)) := inferInstance
  have hQ : Q.LiesOver (span {(l : ℤ)}) := Ideal.LiesOver.trans Q P (span {(l : ℤ)})
  exact ⟨Q, hQp, hQ, fun σ => ⟨inertia_lift P Q σ, fun ⟨τ, h1, h2⟩ => inertia_res P Q σ τ h1 h2⟩,
    fun σ τ h1 h2 => frob_res l P Q σ τ h1 h2⟩

theorem frob_iff_inertia {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] [SMulCommClass G ℤ S]
    (P : Ideal S) (F σ : G) (hF : IsArithFrobAt ℤ F P) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : S, (σ * F⁻¹) • x - x ∈ P := by
  have hF' : ∀ x : S, F • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hF
  constructor
  · intro hσ x
    have hσ' : ∀ x : S, σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P := hσ
    have h1 := P.sub_mem (hσ' (F⁻¹ • x)) (hF' (F⁻¹ • x))
    rwa [smul_inv_smul, ← mul_smul, sub_sub_sub_cancel_right] at h1
  · intro hρ x
    show σ • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    have h1 := P.add_mem (hρ (F • x)) (hF' x)
    rwa [← mul_smul, inv_mul_cancel_right, sub_add_sub_cancel] at h1

end Formalism.HC.Der

end
