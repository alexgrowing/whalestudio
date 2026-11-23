import Mathlib

noncomputable section

namespace GlobalTheory.TraceIso

open Module

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def tr (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] (a : A) : k :=
  LinearMap.trace k V (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem tr_congr (e : V ≃ₗ[A] W) (a : A) : tr k V a = tr k W a := by
  have h : Algebra.lsmul k k W a = (e.restrictScalars k).conj (Algebra.lsmul k k V a) := by
    ext w
    simp [LinearEquiv.conj_apply]
  rw [tr, tr, h, LinearMap.trace_conj']

theorem tr_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by
  have h : Algebra.lsmul k k (V × W) a = (Algebra.lsmul k k V a).prodMap (Algebra.lsmul k k W a) := by
    ext <;> simp
  rw [tr, h, LinearMap.trace_prodMap']
  rfl

theorem tr_one [FiniteDimensional k V] : tr k V (1 : A) = finrank k V := by rw [tr, map_one, LinearMap.trace_one]

theorem finiteDimensional_sub [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := inferInstanceAs (FiniteDimensional k (P.restrictScalars k))

theorem finrank_eq_zero_of_hom [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, tr k V a = tr k W a)
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
  have := h r
  unfold tr at this
  rw [hV, hW, LinearMap.trace_one, map_zero] at this
  exact_mod_cast this

theorem split_of_hom [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by
  obtain ⟨P', hP'⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨Q, hQ⟩ := exists_isCompl (LinearMap.range f)
  let e₁ : V ≃ₗ[A] (LinearMap.ker f) × (LinearMap.range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hP').symm.trans
      ((LinearEquiv.refl A _).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ _ hP').symm.trans f.quotKerEquivRange))
  let e₂ : W ≃ₗ[A] Q × (LinearMap.range f) := (Submodule.prodEquivOfIsCompl _ _ hQ.symm).symm
  haveI := finiteDimensional_sub (k := k) (LinearMap.ker f)
  haveI := finiteDimensional_sub (k := k) (LinearMap.range f)
  haveI := finiteDimensional_sub (k := k) Q
  haveI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h => hf (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank k (LinearMap.range f) := Module.finrank_pos
  refine ⟨_, Q, _, ⟨e₁⟩, ⟨e₂⟩, ?_, ?_⟩
  · rw [(e₁.restrictScalars k).finrank_eq, finrank_prod]; omega
  · rw [(e₂.restrictScalars k).finrank_eq, finrank_prod]; omega

end

theorem nonempty_linear_equiv_of_charpoly_eq [CharZero k] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [tr_congr e₁, tr_congr e₂, tr_prod, tr_prod] at this
      exact add_right_cancel this
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

theorem exists_equiv_of_trace_eq [CharZero k] {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  have key : ∀ a : MonoidAlgebra k Γ, tr k ρ.asModule a = tr k σ.asModule a := by
    intro a
    unfold tr
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have e₁ : LinearMap.trace k _ (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k V (ρ g) := by
        rw [← LinearMap.trace_conj' (ρ g) ρ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      have e₂ : LinearMap.trace k _ (Algebra.lsmul k k σ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k W (σ g) := by
        rw [← LinearMap.trace_conj' (σ g) σ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      rw [e₁, e₂, h]
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

end GlobalTheory.TraceIso

end
