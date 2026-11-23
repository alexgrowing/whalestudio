import Mathlib

namespace GlobalTheory.CompanionTheory.CommSplit

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def compr (W W' : Submodule ℂ V) (hc : IsCompl W W') :
    End ℂ V →ₗ[ℂ] End ℂ W where
  toFun b := (W.linearProjOfIsCompl W' hc) ∘ₗ b ∘ₗ W.subtype
  map_add' b c := by ext w; simp
  map_smul' t b := by ext w; simp

lemma compr_of_inv (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by
  show W.linearProjOfIsCompl W' hc (b w) = _
  exact Submodule.linearProjOfIsCompl_apply_left hc ⟨b w, hb w w.2⟩

lemma compr_eq_restrict (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by
  refine LinearMap.ext fun w => ?_
  rw [compr_of_inv W W' hc b hb w]
  rfl

lemma compr_mul (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, compr_of_inv W W' hc c hcW w]
  rfl

lemma compr_algebraMap (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by
  have hb : ∀ w ∈ W, algebraMap ℂ (End ℂ V) t w ∈ W := fun w hw => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem t hw
  rw [compr_eq_restrict W W' hc _ hb]
  ext w
  simp [Module.algebraMap_end_apply]

lemma adjoin_compr {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨h i, ?_⟩
    rw [compr_eq_restrict W W' hc _ (h i)]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hw
    · rw [compr_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (hx.1 w hw) (hy.1 w hw)
    · rw [map_add]
      exact Subalgebra.add_mem _ hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.End.mul_apply]
      exact hx.1 _ (hy.1 w hw)
    · rw [compr_mul W W' hc x y hy.1]
      exact Subalgebra.mul_mem _ hx.2 hy.2

theorem finrank_adjoin_le_add :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by
  intro V _ _ _ l a W W' hc h h'
  let AW := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : Module.End ℂ W))
  let AW' := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h' i) : Module.End ℂ W'))
  let Φ : Algebra.adjoin ℂ (Set.range a) →ₗ[ℂ] AW × AW' :=
    { toFun := fun b => (⟨compr W W' hc b, (adjoin_compr a W W' hc h b b.2).2⟩,
        ⟨compr W' W hc.symm b, (adjoin_compr a W' W hc.symm h' b b.2).2⟩)
      map_add' := fun b c => by
        ext <;> simp [map_add]
      map_smul' := fun t b => by
        ext <;> simp [map_smul] }
  have hinj : Function.Injective Φ := by
    intro b c hbc
    have h1 := congrArg (fun p => (p.1 : Module.End ℂ W)) hbc
    have h2 := congrArg (fun p => (p.2 : Module.End ℂ W')) hbc
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have e1 : (b : Module.End ℂ V) w = (c : Module.End ℂ V) w := by
      have e := LinearMap.congr_fun h1 ⟨w, hw⟩
      rw [compr_of_inv W W' hc _ (adjoin_compr a W W' hc h b b.2).1,
        compr_of_inv W W' hc _ (adjoin_compr a W W' hc h c c.2).1] at e
      exact congrArg Subtype.val e
    have e2 : (b : Module.End ℂ V) w' = (c : Module.End ℂ V) w' := by
      have e := LinearMap.congr_fun h2 ⟨w', hw'⟩
      rw [compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' b b.2).1,
        compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' c c.2).1] at e
      exact congrArg Subtype.val e
    rw [map_add, map_add, e1, e2]
  calc Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ (AW × AW') :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℂ AW + Module.finrank ℂ AW' := Module.finrank_prod

end GlobalTheory.CompanionTheory.CommSplit
