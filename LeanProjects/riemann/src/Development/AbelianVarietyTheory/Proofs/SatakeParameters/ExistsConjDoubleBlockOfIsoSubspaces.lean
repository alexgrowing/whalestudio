import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.DoubleBlock

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem exists_emb (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : IsInv ρ W) :
    ∃ (σ : Γ →* GL (Fin (Module.finrank k W)) k) (φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W),
      ∀ g x, (φ ((σ g : Matrix _ _ k) *ᵥ x) : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (φ x : Fin a → k) := by
  classical
  let φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W := (Module.finBasis k W).equivFun.symm
  let r : Γ → (W →ₗ[k] W) := fun g =>
    (Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)).restrict (p := W) (q := W) (fun v hv => hW g v hv)
  have hr : ∀ g v, (r g v : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (v : Fin a → k) := fun g v => rfl
  let m : Γ →* Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k :=
    { toFun := fun g => LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        have : r 1 (φ x) = φ x := by
          apply Subtype.ext
          rw [hr]; simp
        simp [this]
      map_mul' := fun g h => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        have : r (g * h) (φ x) = r g (r h (φ x)) := by
          apply Subtype.ext
          rw [hr, hr, hr]; simp
        simp [this] }
  refine ⟨m.toHomUnits, φ, fun g x => ?_⟩
  have : ((m.toHomUnits g : Matrix _ _ k)) *ᵥ x = φ.symm (r g (φ x)) := by
    change LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap) *ᵥ x = _
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, LinearEquiv.apply_symm_apply, hr]

theorem exists_emb_sum (ρ : Γ →* GL (Fin a) k) {d u : ℕ} (σ : Γ →* GL (Fin d) k)
    (τ : Γ →* GL (Fin u) k) (f₁ : (Fin d → k) →ₗ[k] (Fin a → k))
    (f₂ : (Fin u → k) →ₗ[k] (Fin a → k)) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (h₁ : ∀ g x, f₁ ((σ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₁ x)
    (h₂ : ∀ g x, f₂ ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₂ x)
    (hd : Disjoint (LinearMap.range f₁) (LinearMap.range f₂)) :
    ∃ f : (Fin (d + u) → k) →ₗ[k] (Fin a → k), Function.Injective f ∧
      LinearMap.range f = LinearMap.range f₁ ⊔ LinearMap.range f₂ ∧
      ∀ g x, f ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x := by
  let s : (Fin (d + u) → k) ≃ₗ[k] (Fin d → k) × (Fin u → k) :=
    (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ k k)
  have hs : ∀ x, s x = (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i))) :=
    fun x => rfl
  refine ⟨(f₁.coprod f₂) ∘ₗ s.toLinearMap, ?_, ?_, fun g x => ?_⟩
  · have : Function.Injective (f₁.coprod f₂) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
        LinearMap.ker_eq_bot.2 i₁, LinearMap.ker_eq_bot.2 i₂, Submodule.prod_bot]
    exact this.comp s.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]
  · have key : s ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) =
        ((σ g : Matrix _ _ k) *ᵥ (s x).1, (τ g : Matrix _ _ k) *ᵥ (s x).2) := by
      have hM : (SumRepresentations.At.sumRep σ τ g).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (σ g).val 0 0 (τ g).val) := rfl
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, hs, hs]
      ext i <;> simp [Function.comp_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, LinearMap.coprod_apply, h₁, h₂,
      Matrix.mulVec_add]

theorem exists_conj (ρ : Γ →* GL (Fin a) k) {n : ℕ} (τ : Γ →* GL (Fin n) k)
    (f : (Fin n → k) →ₗ[k] (Fin a → k)) (hi : Function.Injective f) (hs : LinearMap.range f = ⊤)
    (h : ∀ g x, f ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x) :
    ∃ (hn : n = a) (Pm : GL (Fin a) k), ∀ g,
      ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr hn) (finCongr hn) ((τ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  classical
  let e := LinearEquiv.ofBijective f ⟨hi, LinearMap.range_eq_top.1 hs⟩
  have hn : n = a := by simpa using e.finrank_eq
  subst hn
  let Pm : GL (Fin n) k := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hP : ∀ x, (Pm : Matrix _ _ k) *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec _ _
  refine ⟨rfl, Pm, fun g => ?_⟩
  have : ρ g * Pm = Pm * τ g := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, h]
  rw [mul_assoc, this, inv_mul_cancel_left]
  simp

theorem exists_conj_double : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  intro k Γ _ _ a ρ W₁ W₂ hss h₁ h₂ hne hdis ⟨e, he⟩
  have h12 : IsInv ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (h₁ g x hx) (h₂ g y hy)
  obtain ⟨U, hU, hc⟩ := hss _ h12
  obtain ⟨σ, φ, hφ⟩ := exists_emb ρ W₁ h₁
  obtain ⟨υ, ψ, hψ⟩ := exists_emb ρ U hU
  have r₁ : LinearMap.range (W₁.subtype ∘ₗ φ.toLinearMap) = W₁ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₂ : LinearMap.range (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) = W₂ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₃ : LinearMap.range (U.subtype ∘ₗ ψ.toLinearMap) = U := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨f, fi, fr, hf⟩ := exists_emb_sum ρ σ σ (W₁.subtype ∘ₗ φ.toLinearMap)
    (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) (W₁.injective_subtype.comp φ.injective)
    (W₂.injective_subtype.comp (φ.trans e).injective) (fun g x => hφ g x)
    (fun g x => by
      have := he g (φ x) (h₁ g _ (φ x).2)
      have h' : φ ((σ g : Matrix _ _ k) *ᵥ x) = ⟨_, h₁ g _ (φ x).2⟩ := Subtype.ext (hφ g x)
      change (e (φ ((σ g : Matrix _ _ k) *ᵥ x)) : Fin a → k) = _
      rw [h', this]
      rfl)
    (by rw [r₁, r₂]; exact disjoint_iff.2 hdis)
  rw [r₁, r₂] at fr
  obtain ⟨F, Fi, Fr, hF⟩ := exists_emb_sum ρ (SumRepresentations.At.sumRep σ σ) υ f (U.subtype ∘ₗ ψ.toLinearMap) fi
    (U.injective_subtype.comp ψ.injective) hf (fun g x => hψ g x)
    (by rw [fr, r₃]; exact hc.disjoint)
  rw [fr, r₃, hc.sup_eq_top] at Fr
  obtain ⟨hn, Pm, hP⟩ := exists_conj ρ _ F Fi Fr hF
  exact ⟨_, _, σ, υ, hn, Pm, Nat.pos_of_ne_zero (fun h0 => hne (Submodule.finrank_eq_zero.1 h0)), hP⟩

end GlobalTheory.DoubleBlock
