import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsoExt

theorem exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by
  obtain ⟨A, hA⟩ := GlobalTheory.FrameFibre.exists_matrix φ hφ hspan (φ' ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := GlobalTheory.FrameFibre.exists_matrix φ' hφ' hspan' (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ' (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ' v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan' fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA',
      Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem exists_unitary_of_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]

end GlobalTheory.IsoExt
