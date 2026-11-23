import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinement
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_block_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)) (tie' : CoordTie ℤ 𝔐.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ ∀ r, (Fl.rootLat r).IsDegOn Set.univ y' (xdeg r) (e r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | exact GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeCpt.Flag.exists_recoord_rootLines <;> assumption)
