import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem exists_latFrame_of_isShortGen : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (Nm : (F →+* ℂ) → V → ℝ) (M : Submodule (𝓞 F) V) (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), Nonempty (LatFrame Nm M) → CompHt.IsShortGen Nm M w abelian₂ → ∃ f : LatFrame Nm M, f.n = n ∧ (∀ x ∈ Submodule.span (𝓞 F) (Set.range f.w.col), x ∈ Submodule.span ℤ (Set.range f.w.col)) ∧ ∀ i σ, ChowHt.frameNorm (f.A σ) (fun a => σ (f.w.col i a)) ≤ abelian₂ := by
  intro F V _ _ _ _ _ _ Nm M n w abelian₂ hf hw
  obtain ⟨f⟩ := hf
  classical
  let e := f.b.equivFun
  let w' : Matrix (Fin f.N) (Fin n) F := Matrix.of fun j k => e (w k) j
  have hcol : w'.col = fun k => e (w k) := rfl
  have hmemM : ∀ i, w i ∈ M := fun i => (hw.gen (w i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hspanO : Submodule.span (𝓞 F) (Set.range w) = M := by
    refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩; exact hmemM i
    · have hz := (hw.gen x).1 hx
      exact Submodule.span_le_restrictScalars ℤ (𝓞 F) _ hz
  have hsum : ∀ k, (∑ j, w' j k • f.b j) = w k := fun k => by
    simp only [w', Matrix.of_apply, e, Module.Basis.equivFun_apply, Module.Basis.sum_repr]
  have hfullV : Submodule.span F (Set.range w) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← f.isFull.2]
    refine Submodule.span_le.2 fun x hx => ?_
    have hz := (hw.gen x).1 hx
    exact Submodule.span_le_restrictScalars ℤ F _ (Submodule.span_mono (le_refl _) hz)
  refine ⟨⟨f.N, n, f.b, w', f.A, ⟨?_, ?_, f.isFrame.herm, f.isFrame.conj, f.isFrame.norm⟩⟩, rfl, ?_, ?_⟩
  · simp only [hsum]; exact hspanO
  · rw [hcol, Set.range_comp', show (⇑e '' Set.range w) = (e.toLinearMap) '' Set.range w from rfl,
      Submodule.span_image, hfullV, Submodule.map_top, LinearEquiv.range]
  · intro x hx
    let eO : V →ₗ[𝓞 F] (Fin f.N → F) := e.toLinearMap.restrictScalars (𝓞 F)
    let eZ : V →ₗ[ℤ] (Fin f.N → F) := e.toLinearMap.restrictScalars ℤ
    have hO : Submodule.span (𝓞 F) (Set.range w'.col) = (Submodule.span (𝓞 F) (Set.range w)).map eO := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    have hZ : Submodule.span ℤ (Set.range w'.col) = (Submodule.span ℤ (Set.range w)).map eZ := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    rw [hO] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hZ]
    exact ⟨y, (hw.gen y).1 (hspanO ▸ hy), rfl⟩
  · intro i σ
    show ChowHt.frameNorm (f.A σ) (fun a => σ (e (w i) a)) ≤ abelian₂
    simp only [e, Module.Basis.equivFun_apply]
    rw [f.isFrame.norm σ (w i)]
    exact hw.le i σ

end GlobalTheory.HSApp
