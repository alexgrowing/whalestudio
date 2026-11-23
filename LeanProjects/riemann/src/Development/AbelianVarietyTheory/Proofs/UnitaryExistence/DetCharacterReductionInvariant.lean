import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne

set_option autoImplicit false

namespace GlobalTheory

open scoped TensorProduct

theorem char_eq_one_of_inverse_det_one_of_basis {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by
  classical
  let φ2 : Module.End S V →* Module.End R V :=
    { toFun := fun g => g.restrictScalars R, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let φ4 : (V ≃ₗ[R] V) →* (Q ≃ₗ[R] Q) :=
    { toFun := fun u => e.trans (u.trans e.symm)
      map_one' := by ext q; simp
      map_mul' := by intro u v; ext q; simp }
  let Φ : GL (Fin r) S →* (Q ≃ₗ[R] Q) :=
    φ4.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      ((Units.map φ2).comp (Units.map ((Matrix.toLinAlgEquiv b :
        Matrix (Fin r) (Fin r) S ≃ₐ[S] Module.End S V) : Matrix (Fin r) (Fin r) S →* Module.End S V))))
  have hdet : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [LinearMap.det_toMatrix, hf]; exact isUnit_one
  let g : GL (Fin r) S := Matrix.nonsingInvUnit _ hdet
  have hg : (g : Matrix (Fin r) (Fin r) S).det = 1 := by
    show (LinearMap.toMatrix b b f).det = 1
    rw [LinearMap.det_toMatrix, hf]
  have h1 : (ψ.comp Φ) g = 1 := generalLinearGroup_char_eq_one_of_det_eq_one S r A (ψ.comp Φ) h4 g hg
  have h2 : Φ g * k = 1 := by
    ext q
    show e.symm ((Matrix.toLinAlgEquiv b (LinearMap.toMatrix b b f)) (e (k q))) = q
    rw [show LinearMap.toMatrix b b f = LinearMap.toMatrixAlgEquiv b f from rfl,
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv, hk, LinearEquiv.symm_apply_apply]
  have h3 := congrArg ψ h2
  rw [map_mul, map_one] at h3
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, one_mul] at h3
  exact h3

private theorem free_quotient_tensor_of_projective {R : Type} [CommRing R] [IsDomain R] (L' : Type)
    [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R)
    [Finite (R ⧸ I)] : Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] L') := by
  refine Module.free_of_flat_of_finrank_eq (R ⧸ I) _ (Module.finrank R L') fun P => ?_
  let := Ideal.Quotient.field P.1
  rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1)
    ((R ⧸ I) ⧸ P.1) L').finrank_eq]
  have h := Module.rankAtStalk_baseChange (R := R) (M := L') (S := (R ⧸ I) ⧸ P.1)
    ⟨⊥, Ideal.isPrime_bot⟩
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] at h
  rw [h]
  exact (Ideal.finrank_fiber_eq_rankAtStalk (M := L') _).symm.trans (Ideal.finrank_fiber_eq_finrank _)

theorem char_eq_one_of_inverse_reduction_det_one : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  intro R _ _ L L' _ _ _ _ _ _ I _ A _ ψ t γ k h4 hsurj hinj hdet hk
  have := free_quotient_tensor_of_projective L' I
  obtain ⟨r, ⟨b⟩⟩ : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) (R ⧸ I) ((R ⧸ I) ⊗[R] L')) := by
    rcases subsingleton_or_nontrivial (R ⧸ I) with h | h
    · have := Module.subsingleton (R ⧸ I) ((R ⧸ I) ⊗[R] L')
      exact ⟨0, ⟨Module.Basis.empty _⟩⟩
    · exact ⟨_, ⟨Module.finBasis (R ⧸ I) ((R ⧸ I) ⊗[R] L')⟩⟩
  have hle : (I • ⊤ : Submodule R L) ≤ (I • ⊤ : Submodule R L').comap t := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  let tb := (I • ⊤ : Submodule R L).mapQ (I • ⊤ : Submodule R L') t hle
  have tbij : Function.Bijective tb := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj a hx)
    · intro y
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a, ha⟩ := hsurj c
      exact ⟨Submodule.Quotient.mk a, ((Submodule.Quotient.eq _).mpr ha).symm⟩
  let e : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (R ⧸ I) ⊗[R] L' :=
    (LinearEquiv.ofBijective tb tbij).trans (TensorProduct.quotTensorEquivQuotSMul L' I).symm
  have he : ∀ a, e (Submodule.Quotient.mk a) = (1 : R ⧸ I) ⊗ₜ[R] t a := by
    intro a
    simp [e, tb, TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  have hz : ∀ x ∈ (I • ⊤ : Submodule R L'), (1 : R ⧸ I) ⊗ₜ[R] x = 0 := by
    intro x hx
    have h0 : (Submodule.Quotient.mk x : L' ⧸ (I • ⊤ : Submodule R L')) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk, h0, map_zero]
  refine char_eq_one_of_inverse_det_one_of_basis b e ψ h4 (LinearMap.baseChange (R ⧸ I) γ) hdet k ?_
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a', ha', hγ⟩ := hk a
  rw [← ha', he, he, LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  exact hz _ hγ

end GlobalTheory
