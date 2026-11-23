import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

theorem twist_left_inverse : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E),
    IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p →
    ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧
      B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  intro X Ω _ ξ E _ _ κ x L m n r φ hT p c₁ hc β hβ
  have hβmem : ∀ a, β a ∈ L p := fun a => by
    rw [hβ.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hw : ∀ a : Fin r, ∃ w : Module.Dual Ω E, ∀ b, w (β b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hβ.1).coord a)
    refine ⟨g, fun b => ?_⟩
    have h1 : g (β b) = ((Module.Basis.span hβ.1).coord a) ((Module.Basis.span hβ.1) b) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : a = b
    · subst h
      simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  choose w hw using hw
  have hwR : ∀ a, ∀ e ∈ L p, w a e ∈ regAt ξ p := by
    intro a e he
    rw [hβ.2] at he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [hw]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | smul s y _ hy =>
      rw [Subring.smul_def, map_smul, smul_eq_mul]
      exact mul_mem s.2 hy
  have hg := fun a => hT.2 p c₁ hc (w a) (hwR a)
  choose g hgR hgw using hg
  refine ⟨Matrix.of fun a j => g a j, fun a j => hgR a j, fun j a => hT.1 j p c₁ hc (β a) (hβmem a), ?_⟩
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [← hgw a (β b) (hβmem b), hw]

end GlobalTheory.CompanionTheory.Ar.FlagBun
