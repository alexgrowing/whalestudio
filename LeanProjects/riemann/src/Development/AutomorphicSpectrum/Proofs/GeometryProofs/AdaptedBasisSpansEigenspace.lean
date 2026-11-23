import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem adaptedFamily_isBasis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W),
    IsAdapted ρH σ v w u → LinearIndependent K v → Module.finrank K (HT.eigSp ρH σ) = p + q →
    FiniteDimensional K (HT.eigSp ρH σ) →
    LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ ρH σ p q v w u hA hv hrank hfd
  obtain ⟨hmem, hfst, hsnd⟩ := hA
  have hz : ∀ j : Fin q, (u (Fin.natAdd p j)).1 = 0 := fun j => (hsnd j).1
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∑ i, g i • (u i).1 = 0 := by
      have := congrArg Prod.fst hg
      simpa [Prod.fst_sum] using this
    have h2 : ∑ i, g i • (u i).2 = 0 := by
      have := congrArg Prod.snd hg
      simpa [Prod.snd_sum] using this
    rw [Fin.sum_univ_add] at h1 h2
    have h1' : ∑ i : Fin p, g (Fin.castAdd q i) • v i = 0 := by
      simpa [hfst, hz] using h1
    have hcast : ∀ i : Fin p, g (Fin.castAdd q i) = 0 :=
      (Fintype.linearIndependent_iff.mp hv) _ h1'
    have h2' : ∑ j : Fin q, g (Fin.natAdd p j) • (u (Fin.natAdd p j)).2 = 0 := by
      simpa [hcast] using h2
    have hnat : ∀ j' : Fin q, g (Fin.natAdd p j') = 0 := by
      intro j'
      have h3 := congrArg (fun f : Module.Dual K W => f (w j')) h2'
      simpa [LinearMap.sum_apply, (hsnd _).2 j'] using h3
    intro i
    induction i using Fin.addCases with
    | left i => exact hcast i
    | right j => exact hnat j
  refine ⟨hli, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hli, Fintype.card_fin, hrank]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
