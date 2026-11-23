import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGOfComb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSAgree.TanLocUnique

theorem comb_unique_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (cf cf' : Fin n → Γ(X, W.1)) (w : Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left), IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w → IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf' w → cf = cf' := by
  intro E _ _ _ H X t U W hW f hf n v hv hb cf cf' w h h'
  have ht : ∀ i, IsTanAtG t (chart W)
      (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) := fun i => by
    have := (GlobalTheory.LocM.FrameBase.tanBasis_baseChange t (X.presheaf.map (homOfLE hW).op).hom _ n v hv hb).1 i
    rwa [GlobalTheory.LogKSDiv.spMap_res_chart U W hW] at this
  have hw : IsTanAtG t (chart W) w := GlobalTheory.RootFrameB.EigTie.isTanAtG_of_comb ht h
  exact (GlobalTheory.LogKSDiv.tanBasis_basicOpen E H X t U W hW f hf n v hv hb w hw).unique h h'

end GlobalTheory.KSAgree.TanLocUnique
