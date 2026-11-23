import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFrameApply
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_tangentCoefficients_unique_affineOpen_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf' w → cf = cf' := by
  first | exact @GlobalTheory.LogKSDiv.generic_coeff_unique | exact GlobalTheory.LogKSDiv.generic_coeff_unique | (intros; apply GlobalTheory.LogKSDiv.generic_coeff_unique <;> assumption)
