import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem HodgeLat.quot_det_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar r 𝓗 σ u hσ hu hspan
  have hvb : (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) := by
    intro p _
    obtain ⟨U, hpU, x, hx⟩ := 𝓗.free p
    refine ⟨U, hpU, fun i => HT.eigProj 𝓗.ρH σ (x i), HodgeDeterminantLattice.span_eigProj σ (hx p hpU), ?_⟩
    intro q _ hq
    refine ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ (hx q hq), ?_⟩
    rw [HodgeLat.quot_apply]
    exact HodgeDeterminantLattice.eigQuot_eq_span σ (hx q hq) (fun a => ⟨⟨σ a, hσ q a⟩, rfl⟩)
  exact ⟨hvb, HodgeDeterminantLattice.detLat_isVB hvb hu hspan, fun p A hA => HodgeDeterminantLattice.detLat_of_frame hu hA⟩

end GlobalTheory.CompanionTheory.Ar.Flat
