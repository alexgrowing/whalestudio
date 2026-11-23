import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

theorem finrank_balBil_le_of_smul_mem_range {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar X) ≤ Module.finrank ℤ (balBil bar Y) := by
  let f' : Y →ₗ[ℤ] X := f.toAddMonoidHom.toIntLinearMap
  have hf' : ∀ y, f' y = f y := fun y => rfl
  let Φ : balBil bar X →ₗ[ℤ] balBil bar Y :=
    { toFun := fun β => ⟨(β : LinearMap.BilinForm ℤ X).compl₁₂ f' f', by
        intro a y z
        have := β.2 a (f y) (f z)
        simpa [hf', LinearMap.compl₁₂_apply, map_smul] using this⟩
      map_add' := fun β β' => by ext; simp
      map_smul' := fun n β => by ext; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext x x'
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨y', hy'⟩ := hf x'
    have h0 : (β : LinearMap.BilinForm ℤ X) (f y) (f y') = 0 := by
      have := congrArg (fun γ : balBil bar Y => (γ : LinearMap.BilinForm ℤ Y) y y') hβ
      simpa [Φ, hf'] using this
    rw [hy, hy'] at h0
    have h1 : ((m : ℤ) * m) * (β : LinearMap.BilinForm ℤ X) x x' = 0 := by
      rw [← h0]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    have hm' : ((m : ℤ) * m) ≠ 0 := by positivity
    simpa using (mul_eq_zero.mp h1).resolve_left hm'
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_balBil_eq_of_finiteIndex {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : Function.Injective f)
    (hr : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar Y) = Module.finrank ℤ (balBil bar X) := by
  let e := LinearEquiv.ofInjective f hf
  let c : X →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (m • LinearMap.id) (fun x => by simpa using hr x)
  let g : X →ₗ[O] Y := e.symm.toLinearMap ∘ₗ c
  have hfg : ∀ x, f (g x) = m • x := by
    intro x
    have h1 : e (g x) = c x := by simp [g]
    have h2 := congrArg Subtype.val h1
    simpa [e, c] using h2
  have hgf : ∀ y, g (f y) = m • y := by
    intro y; apply hf; rw [hfg, map_nsmul]
  apply le_antisymm
  · exact finrank_balBil_le_of_smul_mem_range bar Y X g m hm (fun y => ⟨f y, hgf y⟩)
  · exact finrank_balBil_le_of_smul_mem_range bar X Y f m hm hr

end GlobalTheory.BalRank
