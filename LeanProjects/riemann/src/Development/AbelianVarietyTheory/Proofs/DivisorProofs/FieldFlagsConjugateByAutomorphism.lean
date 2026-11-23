import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.FlagTrans

private theorem exists_adapted_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] {N : ℕ}
    (W : Fin (N + 1) → Submodule K V) (hr : ∀ i, Module.finrank K (W i) = i)
    (hle : ∀ i : Fin N, W i.castSucc ≤ W i.succ) (htop : W (Fin.last N) = ⊤) :
    ∃ b : Module.Basis (Fin N) K V, ∀ i, W i = Submodule.span K (b '' {k | (k : ℕ) < i}) := by
  have hlt (i : Fin N) : W i.castSucc < W i.succ := by
    refine lt_of_le_of_ne (hle i) fun h => ?_
    have h1 := hr i.castSucc
    rw [h, hr] at h1
    simp at h1
  choose v hv hv' using fun i => SetLike.exists_of_lt (hlt i)
  have key (i : Fin (N + 1)) : W i = Submodule.span K (v '' {k | (k : ℕ) < i}) := by
    induction i using Fin.induction with
    | zero =>
      have h0 := hr 0
      simp only [Fin.val_zero, Submodule.finrank_eq_zero] at h0
      simp [h0]
    | succ i ih =>
      have hs : {k : Fin N | (k : ℕ) < (i.succ : Fin (N + 1))} =
          insert i {k : Fin N | (k : ℕ) < (i.castSucc : Fin (N + 1))} := by
        ext k
        simp only [Fin.val_succ, Set.mem_setOf_eq, Fin.val_castSucc, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hs, Set.image_insert_eq, Submodule.span_insert, ← ih]
      have h1 : Submodule.span K {v i} ⊔ W i.castSucc ≤ W i.succ :=
        sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (hv i)) (hle i)
      have h2 : W i.castSucc < Submodule.span K {v i} ⊔ W i.castSucc := by
        refine lt_of_le_of_ne le_sup_right fun h => hv' i ?_
        rw [h]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h3 := Submodule.finrank_lt_finrank_of_lt h2
      refine (Submodule.eq_of_le_of_finrank_le h1 ?_).symm
      rw [hr] at h3 ⊢
      simpa using h3
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← htop, key]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hc : Fintype.card (Fin N) = Module.finrank K V := by
    have := hr (Fin.last N)
    rw [htop, finrank_top] at this
    simp [this]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank v hsp hc, fun i => by
    rw [coe_basisOfTopLeSpanOfCardEqFinrank]; exact key i⟩

private theorem exists_equiv_of_chains {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V] {N : ℕ}
    {A B : Fin (N + 1) → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] V) (g : ∀ i, B i →ₗ[R] V)
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Injective (g i))
    (a : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (A i)) (b : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (B i))
    (hfle : ∀ i : Fin N, LinearMap.range (f i.castSucc) ≤ LinearMap.range (f i.succ))
    (hgle : ∀ i : Fin N, LinearMap.range (g i.castSucc) ≤ LinearMap.range (g i.succ))
    (hft : Function.Surjective (f (Fin.last N))) (hgt : Function.Surjective (g (Fin.last N))) :
    ∃ φ : V ≃ₗ[R] V, ∀ i, ∃ e : A i ≃ₗ[R] B i, ∀ s, g i (e s) = φ (f i s) := by
  letI := hR.toField
  haveI := Module.Finite.of_basis (a (Fin.last N))
  haveI : Module.Finite R V := Module.Finite.of_surjective _ hft
  obtain ⟨u, hu⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (f i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hf i), Module.finrank_eq_card_basis (a i), Fintype.card_fin])
    hfle (LinearMap.range_eq_top.2 hft)
  obtain ⟨w, hw⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (g i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hg i), Module.finrank_eq_card_basis (b i), Fintype.card_fin])
    hgle (LinearMap.range_eq_top.2 hgt)
  refine ⟨u.equiv w (Equiv.refl _), fun i => ?_⟩
  have hmap : (LinearMap.range (f i)).map (u.equiv w (Equiv.refl _) : V →ₗ[R] V) = LinearMap.range (g i) := by
    have h1 := hu i
    have h2 := hw i
    rw [h1, h2, Submodule.map_span, Set.image_image]
    simp
  refine ⟨(LinearEquiv.ofInjective (f i) (hf i)).trans (((u.equiv w (Equiv.refl _)).ofSubmodules _ _ hmap).trans
    (LinearEquiv.ofInjective (g i) (hg i)).symm), fun s => ?_⟩
  simp

variable {X : Scheme.{0}}

private theorem subsingleton_sections_bot (F : X.Modules) : Subsingleton Γ(F, ⊥) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{0}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{1} ↦ i.elim) ⊥ (fun i ↦ i.elim) (by simp) s t (fun i ↦ i.elim)

private theorem eq_bot_or_top [Subsingleton X] (U : X.Opens) : U = ⊥ ∨ U = ⊤ := by
  rcases U.1.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact .inl (TopologicalSpace.Opens.ext h)
  · exact .inr (eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx)

private theorem hom_ext_top [Subsingleton X] {F G : X.Modules} {φ ψ : F ⟶ G}
    (h : ∀ s, φ.app ⊤ s = ψ.app ⊤ s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rcases eq_bot_or_top U with rfl | rfl
  · exact (subsingleton_sections_bot G).elim _ _
  · exact h s

private theorem exists_iso_top [Subsingleton X] {F G : X.Modules} {n : ℕ} {e : Fin n → Γ(F, ⊤)} (he : VB.IsFrame e)
    (g : Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(G, ⊤)) : ∃ φ : F ≅ G, ∀ s, φ.hom.app ⊤ s = g s := by
  have he' : VB.IsFrame fun i => g (e i) := by
    intro V h
    rcases eq_bot_or_top V with rfl | rfl
    · haveI := subsingleton_sections_bot G
      haveI : Subsingleton Γ(X, ⊥) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty rfl)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM G h (g (e i))) =
          g.toLinearMap ∘ₗ Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM F h (e i)) := by
        refine LinearMap.ext fun a => ?_
        simp [Fintype.linearCombination_apply, Twist.resM_self]
      rw [this]
      exact g.bijective.comp (he ⊤ h)
  refine ⟨he.iso he', fun s => ?_⟩
  have : QCoh.appLinear (he.iso he').hom ⊤ = g.toLinearMap := by
    refine (he.basis le_rfl).ext fun i => ?_
    rw [VB.IsFrame.basis_apply, Twist.resM_self, QCoh.appLinear_apply]
    exact he.iso_hom_app he' i
  exact LinearMap.congr_fun this s

private theorem exists_frame_top [Subsingleton X] [Nonempty X] {F : X.Modules} {n : ℕ} (h : VB.IsVB F n) :
    ∃ e : Fin n → Γ(F, ⊤), VB.IsFrame e := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, e, hx, he⟩ := h x
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
  exact ⟨e, he⟩

private theorem range_le {M : X.Modules} {N : ℕ} (F : Vert.Flag M N) (i : Fin N) :
    LinearMap.range (QCoh.appLinear (F.ι i.castSucc) ⊤) ≤ LinearMap.range (QCoh.appLinear (F.ι i.succ) ⊤) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨(F.step i).app ⊤ s, ?_⟩
  rw [← F.step_ι i]
  rfl

end GlobalTheory.FlagTrans

open GlobalTheory.FlagTrans in
theorem _root_.GlobalTheory.T.field_flags_conjugate_by_automorphism : ∀ (L : Type) [Field L] (M : (Spec (CommRingCat.of L)).Modules) (N : ℕ) (F₁ F₂ : Vert.Flag M N), ∃ φ : M ≅ M, ∀ i, ∃ e : F₁.F i ≅ F₂.F i, e.hom ≫ F₂.ι i = F₁.ι i ≫ φ.hom := by
  intro L _ M N F₁ F₂
  have hR : IsField Γ(Spec (CommRingCat.of L), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField L)
  choose a ha using fun i => exists_frame_top (F₁.isVB i)
  choose b hb using fun i => exists_frame_top (F₂.isVB i)
  obtain ⟨m, hm⟩ := exists_frame_top F₁.isVB_self
  obtain ⟨g, hg⟩ := exists_equiv_of_chains hR (fun i => QCoh.appLinear (F₁.ι i) ⊤) (fun i => QCoh.appLinear (F₂.ι i) ⊤)
    (fun i => QCoh.injective_app_of_mono _ _) (fun i => QCoh.injective_app_of_mono _ _)
    (fun i => (ha i).basis le_rfl) (fun i => (hb i).basis le_rfl) (range_le F₁) (range_le F₂)
    (ConcreteCategory.bijective_of_isIso ((F₁.ι (Fin.last N)).app ⊤)).2
    (ConcreteCategory.bijective_of_isIso ((F₂.ι (Fin.last N)).app ⊤)).2
  obtain ⟨φ, hφ⟩ := exists_iso_top hm g
  refine ⟨φ, fun i => ?_⟩
  obtain ⟨e, he⟩ := hg i
  obtain ⟨ψ, hψ⟩ := exists_iso_top (ha i) e
  refine ⟨ψ, hom_ext_top fun s => ?_⟩
  change (F₂.ι i).app ⊤ (ψ.hom.app ⊤ s) = φ.hom.app ⊤ ((F₁.ι i).app ⊤ s)
  rw [hψ, hφ]
  exact he s
