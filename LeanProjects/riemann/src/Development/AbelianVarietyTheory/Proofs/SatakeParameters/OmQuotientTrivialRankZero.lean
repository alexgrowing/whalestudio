import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweZero

section Gen

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_isIrreducible {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := hσ.toNontrivial.exists_pair_ne
  exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem equiv_trivial_of_fixed {σ : Representation ℂ G V} (hσ : σ.IsIrreducible) {v : V} (hv : v ≠ 0)
    (hfix : ∀ g, σ g v = v) : Nonempty (σ.Equiv (Representation.trivial ℂ G ℂ)) := by
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g x hx => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, hfix]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩
  have hS : S = ⊤ := by
    rcases hσ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hv
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have htop : (ℂ ∙ v) = ⊤ := congrArg Subrepresentation.toSubmodule hS
  have hall : ∀ g (x : V), σ g x = x := by
    intro g x
    have : x ∈ ℂ ∙ v := htop ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [map_smul, hfix]
  let e : ℂ ≃ₗ[ℂ] V := (LinearEquiv.toSpanNonzeroSingleton ℂ V v hv).trans (LinearEquiv.ofTop _ htop)
  exact ⟨Representation.Equiv.mk e.symm fun g => by
    ext x
    simp [hall]⟩

theorem fixed_of_tensor_left (e : V ≃ₗ[ℂ] ℂ) (τ : Representation ℂ H W) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) t = t) : ∃ w : W, w ≠ 0 ∧ ∀ h, τ h w = w := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] W := (TensorProduct.congr e (LinearEquiv.refl ℂ W)).trans (TensorProduct.lid ℂ W)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun h => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (1 : Module.End ℂ V) (τ h) s) = τ h (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ht]

theorem fixed_of_tensor_right (e : W ≃ₗ[ℂ] ℂ) (σ : Representation ℂ G V) (t : V ⊗[ℂ] W) (ht0 : t ≠ 0)
    (ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) t = t) : ∃ v : V, v ≠ 0 ∧ ∀ g, σ g v = v := by
  let L : V ⊗[ℂ] W ≃ₗ[ℂ] V := (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  refine ⟨L t, fun h => ht0 (L.injective (by rw [h, map_zero])), fun g => ?_⟩
  have key : ∀ s : V ⊗[ℂ] W, L (TensorProduct.map (σ g) (1 : Module.End ℂ W) s) = σ g (L s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [L]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, ht]

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gl_zero_eq_one (g : GL (Fin 0) k) : g = 1 :=
  Units.ext (Matrix.ext fun i => Fin.elim0 i)

theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

theorem detRep_one (m : ℕ) : detRep (Fin m) (1 : kˣ →* ℂˣ) = Representation.trivial ℂ (GL (Fin m) k) ℂ := by
  unfold detRep ofChar detChar
  rw [MonoidHom.one_comp, twist_one]

theorem om_left (n : ℕ) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin 0) k → ℂ) :
    om (1 : kˣ →* ℂˣ) (1 : GL (Fin 0) k) h Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 j)

theorem om_right (r : ℕ) (g : GL (Fin r) k) (Φ : Matrix (Fin 0) (Fin r) k → ℂ) :
    om (1 : kˣ →* ℂˣ) g (1 : GL (Fin 0) k) Φ = Φ := by
  funext x
  simp [om, nabs_one']
  exact congrArg Φ (Matrix.ext fun i j => Fin.elim0 i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W), r = 0 ∨ n = 0 → σ.IsIrreducible → τ.IsIrreducible → OmQuot 1 σ τ → Nonempty (σ.Equiv (detRep (Fin r) (1 : kˣ →* ℂˣ))) ∧ Nonempty (τ.Equiv (detRep (Fin n) (1 : kˣ →* ℂˣ))) := by
  intro k _ _ _ _ r n V W _ _ _ _ σ τ hrn hσ hτ hq
  obtain ⟨f, hf0, hf⟩ := hq
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, f Φ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  rw [detRep_one, detRep_one]
  rcases hrn with rfl | rfl
  · haveI := nontrivial_of_isIrreducible hσ
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨eσ⟩ := equiv_trivial_of_fixed hσ hv (fun g => by rw [gl_zero_eq_one g, map_one]; rfl)
    have ht : ∀ h, TensorProduct.map (1 : Module.End ℂ V) (τ h) (f Φ) = f Φ := fun h => by
      have := hf 1 h Φ Φ (om_left n h Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨w, hw0, hw⟩ := fixed_of_tensor_left eσ.toLinearEquiv τ _ hΦ ht
    exact ⟨⟨eσ⟩, equiv_trivial_of_fixed hτ hw0 hw⟩
  · haveI := nontrivial_of_isIrreducible hτ
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨eτ⟩ := equiv_trivial_of_fixed hτ hw (fun h => by rw [gl_zero_eq_one h, map_one]; rfl)
    have ht : ∀ g, TensorProduct.map (σ g) (1 : Module.End ℂ W) (f Φ) = f Φ := fun g => by
      have := hf g 1 Φ Φ (om_right r g Φ).symm
      rw [map_one] at this
      exact this.symm
    obtain ⟨v, hv0, hv⟩ := fixed_of_tensor_right eτ.toLinearEquiv σ _ hΦ ht
    exact ⟨equiv_trivial_of_fixed hσ hv0 hv, ⟨eτ⟩⟩

end GlobalTheory.HoweZero
