import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tanEv_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (v : Sp (DualNumber k) ⟶ t.G.left) (hv : IsTanAtG t x v) (k' : Type) [CommRing k'] (φ : k →+* k') (hv' : IsTanAtG t (spMap φ ≫ x) (spMap (Formalism.L2.Pj.dualMap φ) ≫ v)) (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) (s : Γ(GlobalTheory.LieVB.omega t.G, V)), tanEv t hv' h' s = φ (tanEv t hv h s) := by
  first | exact @GlobalTheory.LocM.tanEv_baseChange | exact GlobalTheory.LocM.tanEv_baseChange | (intros; apply GlobalTheory.LocM.tanEv_baseChange <;> assumption)
