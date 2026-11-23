import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartGluing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_gluing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (k : Type) [Field k] a i (φ : Γ(Z.X, (Z.U a).1) →+* k) (ψ : Γ((Y Z.i).X, L.U i) →+* k), spMap ψ ≫ (aff i).fromSpec = spMap φ ≫ Z.chart a ≫ Z.π → ∀ en : En Dw.mult, ∃ hu, spMap φ ≫ Z.chart a ≫ g en = pt (φ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) (plk (fun z : Let Dw.mult => crd i k ψ ((Z.fr a).bc φ z.1 z.2)) en.2.1) hu := by
  first | exact @GlobalTheory.FlagEmb.PlkPt.plk_pt | exact GlobalTheory.FlagEmb.PlkPt.plk_pt | (intros; apply GlobalTheory.FlagEmb.PlkPt.plk_pt <;> assumption)
