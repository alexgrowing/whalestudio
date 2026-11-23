import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  first | exact @GlobalTheory.HeatV.valR_cst_eq_iota | exact GlobalTheory.HeatV.valR_cst_eq_iota | (intros; apply GlobalTheory.HeatV.valR_cst_eq_iota <;> assumption)
