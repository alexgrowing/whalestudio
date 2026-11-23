import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.ThirdIso

open CategoryTheory.Limits

theorem abelian {C : Type*} [Category C] [Abelian C] {A M B L Q V : C}
    (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V)
    (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0)
    (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact)
    (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact)
    (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (hfg : f ≫ g = u) :
    ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧
      q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  have e₀ : Epi q₀ := hS₀.epi_g
  have e₁ : Epi q₁ := hS₁.epi_g
  have e₂ : Epi q₂ := hS₂.epi_g
  have mg : Mono g := hS₁.mono_f
  have c₀ := hS₀.exact.gIsCokernel
  have c₂ := hS₂.exact.gIsCokernel
  have a₀ : f ≫ g ≫ q₂ = 0 := by rw [← Category.assoc, hfg, w₂]
  have a₂ : u ≫ q₁ = 0 := by rw [← hfg, Category.assoc, w₁, comp_zero]
  obtain ⟨l, hl⟩ : ∃ l : L ⟶ V, q₀ ≫ l = g ≫ q₂ :=
    ⟨c₀.desc (CokernelCofork.ofπ _ a₀), c₀.fac (CokernelCofork.ofπ _ a₀) WalkingParallelPair.one⟩
  obtain ⟨m, hm⟩ : ∃ m : V ⟶ Q, q₂ ≫ m = q₁ :=
    ⟨c₂.desc (CokernelCofork.ofπ _ a₂), c₂.fac (CokernelCofork.ofπ _ a₂) WalkingParallelPair.one⟩
  have w₃ : l ≫ m = 0 := by
    rw [← cancel_epi q₀, comp_zero, ← Category.assoc, hl, Category.assoc, hm, w₁]
  refine ⟨l, m, w₃, ?_, hl, hm⟩
  have em : Epi m := by
    subst hm
    exact epi_of_epi q₂ m
  have ml : Mono l := by
    refine Preadditive.mono_of_cancel_zero _ ?_
    intro T x hx
    obtain ⟨T₁, p₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi q₀ x
    have hy0 : (y ≫ g) ≫ q₂ = 0 := by
      rw [Category.assoc, ← hl, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    obtain ⟨T₂, p₂, _, z, hz⟩ :=
      (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS₂.exact (y ≫ g) hy0
    dsimp at hz
    have hz' : p₂ ≫ y = z ≫ f := by
      rw [← cancel_mono g, Category.assoc, Category.assoc, hfg, hz]
    rw [← cancel_epi (p₂ ≫ p₁), comp_zero, Category.assoc, hy, ← Category.assoc, hz',
      Category.assoc, w₀, comp_zero]
  have ex : (ShortComplex.mk l m w₃).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at x hx
    obtain ⟨T₁, p₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi q₂ x
    have hy0 : y ≫ q₁ = 0 := by
      rw [← hm, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
    obtain ⟨T₂, p₂, _, z, hz⟩ :=
      (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS₁.exact y hy0
    dsimp at hz
    refine ⟨T₂, p₂ ≫ p₁, inferInstance, z ≫ q₀, ?_⟩
    dsimp
    rw [Category.assoc, hy, ← Category.assoc, hz, Category.assoc, Category.assoc, hl]
  exact { exact := ex, mono_f := ml, epi_g := em }

end GlobalTheory.ThirdIso

theorem GlobalTheory.ThirdIso.modules : ∀ (X : Scheme.{0}) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact), f ≫ g = u → ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0), (ShortComplex.mk l m w₃).ShortExact ∧ q₀ ≫ l = g ≫ q₂ ∧ q₂ ≫ m = q₁ := by
  intro X A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hfg
  exact GlobalTheory.ThirdIso.abelian f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hfg
