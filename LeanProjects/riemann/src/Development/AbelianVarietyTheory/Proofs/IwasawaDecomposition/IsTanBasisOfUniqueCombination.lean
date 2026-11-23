import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in

theorem GlobalTheory.LineNorm.isTanBasis_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x e cf u) → GlobalTheory.LineNorm.IsTanBasis t x e := by
  intro E _ _ _ H X t R _ x g e he hb
  let v : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun i => tanOf (he i)
  have hv : Full v := fun n => (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff v a n).1 (hb _ (isTan_tv n))
  refine ⟨he, fun S _ φ w hw => ?_⟩
  have h := full_bc φ hv (tanOf hw)
  exact (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff (fun i => resM φ (v i)) a (tanOf hw)).2 h
