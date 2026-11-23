import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagBundleFamily
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_flag_bundle_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (ι : Type) (rk : ι → ℕ) (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a)) (Bs Bg Y : Scheme.{0}) (M : ι → Bs.Modules) (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)), (∀ a, IsLieFrames Z e jB πB (M a) (rk a) (emb a) (dual a) (u a)) → Function.Bijective emb → ∀ (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (χ : c.F →+* K), y ≫ π = xb ≫ jB → xb ≫ πB ≫ genStr Z = spMap χ → ∀ x : Sp K ⟶ Z.X, x = xb ≫ πB ≫ genι Z → ∃ g : EigFrame Z χ x, Bears Z emb dual hr hM jB πB u π fl y xb g := by
  first | exact @GlobalTheory.FlagCls.exists_bears | exact GlobalTheory.FlagCls.exists_bears | (intros; apply GlobalTheory.FlagCls.exists_bears <;> assumption)
