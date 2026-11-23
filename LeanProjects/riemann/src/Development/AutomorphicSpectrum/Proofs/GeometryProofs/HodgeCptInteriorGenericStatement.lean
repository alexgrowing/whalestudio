import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_interior_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), Function.Injective β → 𝔐.Interior 𝔐.ξ ∧ (∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j) ∧ CharZero Ω ∧ Function.Injective 𝔐.emb ∧ (∀ s, Module.finrank Ω (𝔐.Vgen s) = labelRk D s) ∧ (⨆ s, 𝔐.Vgen s) = ⊤ ∧ iSupIndep 𝔐.Vgen ∧ ∀ s a (q : Cpt 𝔐.ξ), 𝔐.emb s a ∈ regAt 𝔐.ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic | exact GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic <;> assumption)
