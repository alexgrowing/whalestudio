import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelOfAtlas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_of_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → Geo (Y i) π → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X), Z'.i = i ∧ Z'.ty = ty ∧ (∀ (Z₁ : Mdl Y i₀) (g : Z₁.X ⟶ X), MapsTo Z₁ A g → MapsTo Z₁ (atlasOf Z') (g ≫ e.inv)) ∧ (∀ (X₂ : Scheme.{0}) (π₂ : X₂ ⟶ (Y i).X) (ty₂ : (E →+* ℂ) → Finset ℕ) (A₂ : Atlas (Y i) π₂ ty₂) (f : X ⟶ X₂), f ≫ π₂ = π → (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y i).t K), A.FlagAt w u → A₂.FlagAt (w ≫ f) u) → MapsTo Z' A₂ (e.hom ≫ f)) ∧ ∀ σ k, IntStep A σ k → IntStep (atlasOf Z') σ k := by
  first | exact @GlobalTheory.DRFlag.exists_mdl_of_atlas | exact GlobalTheory.DRFlag.exists_mdl_of_atlas | (intros; apply GlobalTheory.DRFlag.exists_mdl_of_atlas <;> assumption)
