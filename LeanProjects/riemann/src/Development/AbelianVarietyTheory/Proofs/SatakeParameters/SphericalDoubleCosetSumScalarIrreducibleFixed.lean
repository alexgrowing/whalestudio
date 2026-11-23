import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HeckeScalarDC

open GlobalTheory.HeckeScalarSph

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem dc_scalar_fin (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (s : SplitPlace L) (α : GAf L n) (hα : TrivOutside {s.v} α) (Rα : Finset (GAf L n))
    (hRα0 : (∀ γ ∈ Rα, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ Rα ∧ γ⁻¹ * x ∈ Umax L n) :
    ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      ∑ γ ∈ Rα, NG.rt L n γ f = c • f := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα hRα0
  have hRtriv : ∀ γ ∈ Rα, TrivOutside {s.v} γ := by
    intro γ hγ
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hRα0.1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ Rα, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ Rα, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b Rα (R b) hα hb (fun y hy => hRα0.2 y (conv.1 hy))
        (fun γ hγ => conv.2 (hRα0.1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [← e]
  rfl

theorem dc_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS s α hα ι R r h1 h2
  classical
  have hinj : Set.InjOn r R := by
    intro γ hγ δ hδ e
    have hx := h1 γ hγ
    have hU : (r γ)⁻¹ * r γ ∈ Umax L n := by rw [inv_mul_cancel]; exact one_mem _
    exact (h2 (r γ) hx).unique ⟨hγ, hU⟩ ⟨hδ, by rw [← e]; exact hU⟩
  have hA : ∀ γ ∈ R.image r, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    exact h1 δ hδ
  have hB : ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) →
      ∃! γ, γ ∈ R.image r ∧ γ⁻¹ * x ∈ Umax L n := by
    intro x hx
    obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h2 x hx
    refine ⟨r γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hy
    rw [hu δ ⟨hδ, ey⟩]
  obtain ⟨c, hc⟩ := dc_scalar_fin a S hS s α hα (R.image r) ⟨hA, hB⟩
  refine ⟨c, fun f hf hfix => ?_⟩
  rw [← hc f hf hfix, Finset.sum_image (fun γ hγ δ hδ e => hinj hγ hδ e)]

end GlobalTheory.HeckeScalarDC

end
