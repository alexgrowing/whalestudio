import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_local_ring_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀) (R K k : Type) [CommRing R] [IsLocalRing R] [Field K] [Field k] (φ : R →+* K) (ψ : R →+* k) (z : Sp R ⟶ Z.X) (z' : Sp R ⟶ X), i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → Function.Injective φ → z (IsLocalRing.closedPoint R) ∈ Z.opn → NatTo Z A (spMap φ ≫ z) (spMap φ ≫ z') → NatTo Z A (spMap ψ ≫ z) (spMap ψ ≫ z') := by
  first | exact @GlobalTheory.DRFlag.Spez.natTo_specialise | exact GlobalTheory.DRFlag.Spez.natTo_specialise | (intros; apply GlobalTheory.DRFlag.Spez.natTo_specialise <;> assumption)
