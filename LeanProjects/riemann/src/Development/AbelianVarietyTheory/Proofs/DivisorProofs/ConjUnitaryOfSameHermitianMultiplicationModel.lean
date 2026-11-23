import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem models_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ γ' : GLw n w), IsModel w e B u x γ → IsModel w e B u x γ' → ∃ y ∈ UL n w, γ' = y⁻¹ * γ * y := by
  intro E _ _ _ w hw K e B u x n γ γ' hγ hγ'
  obtain ⟨ψ, hψl, hψu, hψh⟩ := hγ
  obtain ⟨ψ', hψ'l, hψ'u, hψ'h⟩ := hγ'
  let f : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ (ψ'.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψ'l, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψl] }
  let g : (Fin n → w.adicCompletion E) →ₗ[w.adicCompletion E] (Fin n → w.adicCompletion E) :=
    { toFun := fun v => ψ' (ψ.symm v)
      map_add' := by intro a b; simp
      map_smul' := by
        intro t v
        obtain ⟨c, rfl⟩ : ∃ c, e c = t := ⟨e.symm t, e.apply_symm_apply t⟩
        obtain ⟨a, rfl⟩ : ∃ a, ψ a = v := ⟨ψ.symm v, ψ.apply_symm_apply v⟩
        simp only [RingHom.id_apply]
        rw [← hψl, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hψ'l] }
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  have hgf : g ∘ₗ f = LinearMap.id := LinearMap.ext fun v => by simp [f, g]
  let y : GLw n w := ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g,
    by rw [← LinearMap.toMatrix'_comp, hfg, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, hgf, LinearMap.toMatrix'_id]⟩
  have hy : ∀ v, (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ v = f v := fun v =>
    LinearMap.toMatrix'_mulVec f v

  have hinv : ∀ v v', stdH w (f v) (f v') = stdH w v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
    obtain ⟨b, rfl⟩ : ∃ b, ψ' b = v' := ⟨ψ'.symm v', ψ'.apply_symm_apply v'⟩
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
    rw [hψh, hψ'h]
  refine ⟨y, ?_, ?_⟩
  · unfold UL
    rw [if_neg hw]
    change Formalism.UG.cT (cj w) (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * 1 *
      (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1
    set M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hM
    have key : Mᵀ * M.map (cj w) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 := hinv (Pi.single i 1) (Pi.single j 1)
      rw [← hy, ← hy] at h1
      simp only [stdH, Matrix.mulVec_single_one] at h1
      have h2 : (if i = j then (1 : w.adicCompletion E) else 0) = ∑ k, M k i * cj w (M k j) := by
        simpa [Pi.single_apply, eq_comm] using h1
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      exact h2.symm
    have key2 := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at key2
    rw [Matrix.mul_one]
    exact key2
  ·
    have hc : (y : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * γ'.val = γ.val * y := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨a, rfl⟩ : ∃ a, ψ' a = v := ⟨ψ'.symm v, ψ'.apply_symm_apply v⟩
      simp only [Matrix.toLin'_apply]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hψ'u, hy, hy]
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, AddEquiv.symm_apply_apply]
      rw [hψu]
    have hc' : y * γ' = γ * y := Units.ext hc
    rw [mul_assoc, ← hc', ← mul_assoc, inv_mul_cancel, one_mul]

end GlobalTheory.KapLat
