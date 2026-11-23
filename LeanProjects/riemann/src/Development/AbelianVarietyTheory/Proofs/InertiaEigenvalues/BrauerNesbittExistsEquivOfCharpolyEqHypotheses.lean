import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq

noncomputable section

namespace GlobalTheory.CharpolyIso

open Module Polynomial GlobalTheory.TraceIso

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cp (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Module A V] [IsScalarTower k A V] (a : A) : k[X] :=
  LinearMap.charpoly (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [FiniteDimensional k V] [FiniteDimensional k W]

theorem cp_congr (e : V ≃ₗ[A] W) (a : A) : cp k V a = cp k W a := by
  unfold cp
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k) (Algebra.lsmul k k V a)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

theorem cp_prod (a : A) : cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem charpoly_one_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (1 : V →ₗ[k] V) = (X - 1 : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), LinearMap.toMatrix_one,
    Matrix.charpoly_one]
  simp

theorem charpoly_zero_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (0 : V →ₗ[k] V) = (X : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), map_zero, Matrix.charpoly_zero]
  simp

theorem finrank_eq_zero_of_hom
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, cp k V a = cp k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have key := h r
  unfold cp at key
  rw [hV, hW, charpoly_one_eq, charpoly_zero_eq] at key
  have hdeg : finrank k V = finrank k W := by
    have := congrArg natDegree key
    have h1 : (X - 1 : k[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : k)
    simpa [natDegree_pow, h1] using this
  have h0 := congrArg (Polynomial.eval 0) key
  simp only [eval_pow, eval_sub, eval_X, eval_one, zero_sub] at h0
  by_contra hne
  have hW0 : finrank k W ≠ 0 := hdeg ▸ hne
  rw [zero_pow hW0] at h0
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h0

end

theorem nonempty_linear_equiv_of_charpoly_eq (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [cp_congr e₁, cp_congr e₂, cp_prod, cp_prod] at this
      have hS : cp k S a ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
      exact mul_right_cancel₀ hS this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem cp_asModule {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Γ V) (a : MonoidAlgebra k Γ) :
    haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
    cp k ρ.asModule a = LinearMap.charpoly (ρ.asAlgebraHom a) := by
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  unfold cp
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv.symm (ρ.asAlgebraHom a)]
  congr 1

theorem exists_equiv_of_charpoly_eq {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ a : MonoidAlgebra k Γ,
      LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  haveI : FiniteDimensional k σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  have key : ∀ a : MonoidAlgebra k Γ, cp k ρ.asModule a = cp k σ.asModule a := fun a => by
    rw [cp_asModule, cp_asModule, h]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

theorem exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V)
    (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
    (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) =
      LinearMap.charpoly (σ.asAlgebraHom a)) →
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) :=
  fun ρ σ hρ hσ h => exists_equiv_of_charpoly_eq ρ σ hρ hσ h

end GlobalTheory.CharpolyIso

end
