import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RayLift

theorem exists_flat_lift (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (z : (DegPre.BF Q (FractionRing R)).left) :
    ∃ (Z : Scheme.{0}) (p : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (w : Z) (y : Z ⟶ Y.H.left),
      p w = z ∧ Epi p ∧ Function.Injective (p.stalkMap w).hom ∧
        y ≫ Y.q.left = p ≫ (DegPre.prB Q (FractionRing R)).left := by
  obtain ⟨hF, hS, -⟩ := GlobalTheory.Heat.Descend.q_props Y
  let p := pullback.fst (DegPre.prB Q (FractionRing R)).left Y.q.left
  have hpF : Flat p := by haveI := hF; dsimp [p]; infer_instance
  have hpS : Surjective p := by haveI := hS; dsimp [p]; infer_instance
  obtain ⟨w, hw⟩ := p.surjective z
  refine ⟨_, p, w, pullback.snd _ _, hw, Flat.epi_of_flat_of_surjective p, ?_, pullback.condition.symm⟩
  let _ := (p.stalkMap w).hom.toAlgebra
  have : Module.Flat _ _ := Flat.stalkMap p w
  have : IsLocalHom (algebraMap ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w)) :=
    inferInstanceAs (IsLocalHom (p.stalkMap w).hom)
  have : Module.FaithfullyFlat ((DegPre.BF Q (FractionRing R)).left.presheaf.stalk (p w)) ((pullback (DegPre.prB Q (FractionRing R)).left Y.q.left).presheaf.stalk w) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective _ _

end GlobalTheory.RayLift
