import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPHeckeTranslateHarrisTaylorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_isHeckeMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 →
    ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hEF hg hck M M'
  obtain ⟨o', ψ, hψ⟩ := GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor p D R b g c k N hc hk hN hNp hEF hg hck M'.X M'.s M'.univ
  obtain ⟨π, ⟨hπ, hm⟩, -⟩ := M.toRepFam.rep M'.X M'.s o'
  exact ⟨π, hπ, o', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.Hecke
