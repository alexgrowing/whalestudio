import Mathlib

namespace GlobalTheory.CompanionTheory.LocHom

variable {R : Type*} [CommRing R]

theorem isLocalizedModule_of_retract {M M' N N' : Type*} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R M'] [Module R N] [Module R N']
    (S : Submonoid R) (g : M →ₗ[R] M') (h : N →ₗ[R] N') [IsLocalizedModule S h]
    (i : M →ₗ[R] N) (j : N →ₗ[R] M) (i' : M' →ₗ[R] N') (j' : N' →ₗ[R] M')
    (hji : ∀ x, j (i x) = x) (hji' : ∀ x, j' (i' x) = x)
    (hi : ∀ x, h (i x) = i' (g x)) (hj : ∀ y, g (j y) = j' (h y)) :
    IsLocalizedModule S g := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [Module.End.isUnit_iff]
    have hu := IsLocalizedModule.map_units h s
    rw [Module.End.isUnit_iff] at hu
    constructor
    · intro x y hxy
      apply (show Function.Injective i' from fun a b e => by rw [← hji' a, ← hji' b, e])
      apply hu.1
      simp only [Module.algebraMap_end_apply] at hxy ⊢
      rw [← map_smul, ← map_smul, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hu.2 (i' y)
      refine ⟨j' z, ?_⟩
      simp only [Module.algebraMap_end_apply] at hz ⊢
      rw [← map_smul, hz, hji']
  · intro y
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalizedModule.surj S h (i' y)
    refine ⟨⟨j x, s⟩, ?_⟩
    simp only at hx ⊢
    rw [hj, ← hx, Submonoid.smul_def, Submonoid.smul_def, map_smul, hji']
  · intro x₁ x₂ e
    have h0 : h (i x₁) = h (i x₂) := by rw [hi, hi, e]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    refine ⟨c, ?_⟩
    have h1 := congrArg j hc
    simpa only [Submonoid.smul_def, map_smul, hji] using h1

theorem map_away_smul {f : R} {P D : Type*} [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [CommRing D] [Algebra R D] (ρ : Localization.Away f →ₐ[R] D) (φ : P →ₗ[R] D)
    (a : Localization.Away f) (p : P) : φ (a • p) = ρ a * φ p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers f) a
  simp only at hrs
  have hs : IsUnit (algebraMap R D s) := by
    have := (IsLocalization.map_units (Localization.Away f) s).map ρ
    rwa [AlgHom.commutes] at this
  have h1 : (s : R) • (a • p) = r • p := by
    rw [← algebraMap_smul (Localization.Away f) (s : R), ← algebraMap_smul (Localization.Away f) r,
      ← hrs, smul_smul, mul_comm]
  have h2 : (s : R) • φ (a • p) = r • φ p := by rw [← map_smul, h1, map_smul]
  rw [Algebra.smul_def, Algebra.smul_def] at h2
  have h3 := congrArg ρ hrs
  rw [map_mul, AlgHom.commutes, AlgHom.commutes] at h3
  apply hs.mul_right_injective
  show algebraMap R D s * _ = algebraMap R D s * _
  linear_combination h2 - φ p * h3

section retraction

variable {A P D : Type*} [CommRing A] [Algebra R A] [AddCommGroup P] [Module R P]
  [CommRing D] [Algebra R D] {n : ℕ}

noncomputable def coord (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) (k : Fin n) : P →ₗ[R] D :=
  ρ.toLinearMap ∘ₗ LinearMap.proj k ∘ₗ s

noncomputable def assemble (s : P →ₗ[R] (Fin n → A)) (ρ : A →ₐ[R] D) :
    (Fin n → D) →ₗ[R] (P →ₗ[R] D) where
  toFun v := ∑ k, v k • coord s ρ k
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, smul_assoc]

def evalAt (D : Type*) [CommRing D] [Algebra R D] (b : Fin n → P) :
    (P →ₗ[R] D) →ₗ[R] (Fin n → D) where
  toFun φ k := φ (b k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end retraction

theorem isLocalizedModule_compRight_away :
    ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (f t : R) [AddCommGroup P] [Module R P]
      [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
      [Module.Finite (Localization.Away f) P]
      [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) →
      ∀ c : C →ₐ[R] C',
      IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
      IsLocalizedModule (Submonoid.powers t)
        (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  intro R P C C' _ _ _ _ _ f t _ _ _ _ _ _ hf c hc
  have hunit : ∀ y : Submonoid.powers f, IsUnit ((Algebra.ofId R C) (y : R)) := by
    rintro ⟨_, k, rfl⟩
    simpa [Algebra.ofId_apply] using hf.pow k
  let ρ : Localization.Away f →ₐ[R] C := IsLocalization.liftAlgHom (M := Submonoid.powers f) hunit
  let ρ' : Localization.Away f →ₐ[R] C' := c.comp ρ
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (Localization.Away f) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let s₀ : P →ₗ[R] (Fin n → Localization.Away f) := s.restrictScalars R
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  have hret : ∀ {D : Type} [CommRing D] [Algebra R D] (σ : Localization.Away f →ₐ[R] D)
      (φ : P →ₗ[R] D), assemble s₀ σ (evalAt D b φ) = φ := by
    intro D _ _ σ φ
    ext p
    conv_rhs => rw [← hexp p]
    simp [assemble, evalAt, coord, s₀, map_sum, map_away_smul σ, mul_comm]
  haveI : IsLocalizedModule (Submonoid.powers t)
      (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k) :=
    IsLocalizedModule.pi (Submonoid.powers t) (fun _ : Fin n => c.toLinearMap)
  refine isLocalizedModule_of_retract (Submonoid.powers t) _
    (LinearMap.pi fun k : Fin n => c.toLinearMap ∘ₗ LinearMap.proj k)
    (evalAt C b) (assemble s₀ ρ) (evalAt C' b) (assemble s₀ ρ')
    (hret ρ) (hret ρ') ?_ ?_
  · intro φ
    rfl
  · intro v
    ext p
    simp [assemble, coord, ρ', map_sum]

end GlobalTheory.CompanionTheory.LocHom
