import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.PullField

theorem isInv_pbT_single : ∀ (R : Type) [CommRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) (u : TanM (𝟙 (Sp R)) B) (dd : Fld G.left) (e : Fld B.left), tv v ≫ q = tv u → IsInv G v dd → IsInv B u e → ∀ (V : B.left.Opens) (W : G.left.Opens), W ≤ q.left ⁻¹ᵁ V → ∀ f : Γ(B.left, V), dd W (pbT q.left f W) = pbT q.left (e V f) W := by
  intro R _ G B _ _ _ _ q _ v u dd e hvu hd he V W hW f
  have hc : GlobalTheory.Heat.LiePush.pushL q v = ∑ a : Fin 1, (fun _ => (1 : R)) a • (fun _ => u) a := by
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext hvu
  rw [GlobalTheory.Heat.LiePush.isInv_pbT q hd (fun _ => he) (fun _ => 1) hc V f W hW]
  congr 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  simp [constFn]

end GlobalTheory.Heat.PullField
