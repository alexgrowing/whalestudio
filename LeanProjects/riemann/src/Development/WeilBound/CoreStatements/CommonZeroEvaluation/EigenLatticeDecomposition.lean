import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

open NumberField
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace ModelDimension

open scoped TensorProduct in
theorem chars_injective {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {ι : Type} [Fintype ι]
    (emb : ι → (𝓞 E →+* Ω)) (hinj : Function.Injective emb) (hcard : Fintype.card ι = Module.finrank ℚ E)
    (Φ : Ω ⊗[ℤ] 𝓞 E →ₗ[Ω] (ι → Ω)) (hΦ : ∀ a j, Φ (1 ⊗ₜ a) j = emb j a) : Function.Injective Φ := by
  have hli : LinearIndependent Ω (fun j => (emb j : 𝓞 E → Ω)) :=
    (linearIndependent_monoidHom (𝓞 E) Ω).comp (fun j => (emb j : 𝓞 E →* Ω))
      (fun i j h => hinj (RingHom.ext fun a => DFunLike.congr_fun h a))
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hs : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, funext fun j => hΦ a j⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2 hs
  rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_fintype_fun_eq_card, hcard]

theorem eigen_lattice_decomposition : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (F₀ : Subfield Ω) (B A : Subring Ω), (∀ x ∈ F₀, x ∈ B) → B ≤ A → ∀ (ι : Type) [Fintype ι] (emb : ι → (𝓞 E →+* Ω)), Function.Injective emb → Fintype.card ι = Module.finrank ℚ E → (∀ i a, emb i a ∈ F₀) → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (ρ : 𝓞 E →+* Module.End Ω Li) (L : Submodule B Li), (∀ a, ∀ e ∈ L, ρ a e ∈ L) → ∀ (i : ι) (e : Li), e ∈ Submodule.span A (L : Set Li) → e ∈ eigSp ρ (emb i) → e ∈ Submodule.span A ((L ⊓ (eigSp ρ (emb i)).restrictScalars B : Submodule B Li) : Set Li) := by
  intro E _ _ Ω _ _ F₀ B A hFB hBA ι _ emb hinj hcard hF Li _ _ ρ L hL i e he hei
  classical
  have hne : ∀ j, ∃ a, j ≠ i → emb i a ≠ emb j a := fun j => by
    by_contra h
    push Not at h
    exact (h 0).1 (hinj (RingHom.ext fun a => (h a).2.symm))
  choose a ha using hne
  let Φ : TensorProduct ℤ Ω (𝓞 E) →ₐ[Ω] (ι → Ω) :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω _) (RingHom.pi emb).toIntAlgHom fun _ _ => Commute.all _ _
  let Ψ : TensorProduct ℤ Ω (𝓞 E) →ₐ[Ω] Module.End Ω Li :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω _) ρ.toIntAlgHom fun x y => Algebra.commutes x _
  have hΦ : ∀ b j, Φ (1 ⊗ₜ b) j = emb j b := fun b j => by
    have := Algebra.TensorProduct.lift_tmul (Algebra.ofId Ω _) (RingHom.pi emb).toIntAlgHom
      (fun _ _ => Commute.all _ _) 1 b
    rw [map_one, one_mul] at this
    exact congrFun this j
  have hΨ : ∀ b, Ψ (1 ⊗ₜ b) = ρ b := fun b => by
    have := Algebra.TensorProduct.lift_tmul (Algebra.ofId Ω _) ρ.toIntAlgHom
      (fun x y => Algebra.commutes x _) 1 b
    rw [map_one, one_mul] at this
    exact this
  have hΦi : Function.Injective Φ := chars_injective emb hinj hcard Φ.toLinearMap hΦ
  let t : ι → TensorProduct ℤ Ω (𝓞 E) := fun j =>
    (emb i (a j) - emb j (a j))⁻¹ • (1 ⊗ₜ a j - algebraMap Ω _ (emb j (a j)))
  have ht : ∀ j x, Ψ (t j) x = (emb i (a j) - emb j (a j))⁻¹ • (ρ (a j) x - emb j (a j) • x) := fun j x => by
    simp only [t, map_smul, map_sub, hΨ, AlgHom.commutes, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]
  let p := ∏ j ∈ Finset.univ.erase i, t j
  have hmem : ∀ x, x ∈ eigSp ρ (emb i) ↔ ∀ b, ρ b x = emb i b • x := fun x => by
    simp [eigSp, sub_eq_zero]
  have h1 : ∀ x ∈ L, Ψ p x ∈ L := by
    refine Finset.prod_induction _ (fun q => ∀ x ∈ L, Ψ q x ∈ L) (fun q r hq hr x hx => ?_) (fun x hx => ?_)
      fun j _ x hx => ?_
    · rw [map_mul]; exact hq _ (hr x hx)
    · rw [map_one]; exact hx
    · rw [ht]
      exact L.smul_mem (⟨_, hFB _ (inv_mem (sub_mem (hF i _) (hF j _)))⟩ : B)
        (sub_mem (hL _ x hx) (L.smul_mem (⟨_, hFB _ (hF j _)⟩ : B) hx))
  have h2 : ∀ x ∈ eigSp ρ (emb i), Ψ p x = x := by
    refine Finset.prod_induction _ (fun q => ∀ x ∈ eigSp ρ (emb i), Ψ q x = x) (fun q r hq hr x hx => ?_)
      (fun x hx => ?_) fun j hj x hx => ?_
    · rw [map_mul, Module.End.mul_apply, hr x hx, hq x hx]
    · rw [map_one]; rfl
    · rw [ht, (hmem x).1 hx, ← sub_smul, smul_smul,
        inv_mul_cancel₀ (sub_ne_zero.2 (ha j (Finset.ne_of_mem_erase hj))), one_smul]
  have h3 : ∀ x, Ψ p x ∈ eigSp ρ (emb i) := fun x => (hmem _).2 fun b => by
    have hz : (1 ⊗ₜ b - algebraMap Ω _ (emb i b)) * p = 0 := by
      apply hΦi
      rw [map_zero, map_mul]
      funext k
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hk : k = i
      · subst hk
        rw [map_sub, Pi.sub_apply, hΦ, AlgHom.commutes]
        simp
      · apply mul_eq_zero_of_right
        simp only [p, map_prod, Finset.prod_apply]
        refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) ?_
        simp only [t, map_smul, map_sub, AlgHom.commutes, Pi.smul_apply, Pi.sub_apply, hΦ]
        simp
    have h4 := congrArg (fun q => Ψ q x) hz
    simp only [map_mul, map_sub, hΨ, AlgHom.commutes, map_zero, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply, LinearMap.zero_apply] at h4
    exact sub_eq_zero.1 h4
  rw [← h2 e hei]
  clear hei
  induction he using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨h1 x hx, h3 x⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

end ModelDimension
