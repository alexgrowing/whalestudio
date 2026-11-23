import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericAmpleDvr

theorem triv_theta {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) :=
  CubeNoeth.triv_of_faces allSixLaws.1.globalFns hA hL (thφ A (x3 A)) thε
    (fun r i b h => AbLaw.CubeGen.trivAt_of_formal hL r (AbLaw.CubeGen.prod_face r i b h))
    (fun r b h => AbLaw.CubeGen.prod_face r 0 b h)

theorem relAmple_of_generic_principal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] (A : Over (Sp (FractionRing V))) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (LA : LB A.left) (ψ : LB.Iso LA (L.pull φ)), IsAbelianScheme G → IsAbelianScheme A → L.IsLB → LA.IsLB → IsGrpPullback A G (jK V) φ → ψ.IsGen → RelAmple A LA → KTriv A LA → RelAmple G L := by
  intro V _ _ _ _ _ G _ A _ φ L LA ψ hG _ hL hLA h hψ ha hk
  have := hG.comm
  have hr : Rigidified G L := DVR.exists_gen_of_isLB_local (V := V) _ (pull_isLB hL _)
  obtain ⟨M, rfl, ⟨c⟩⟩ := Moduli.cubicalStr_of_triv_theta allSixLaws.1 _ G hG L hL hr (triv_theta hG hL)
  exact GoodPol.relAmple_of_generic allSixLaws.1 hG c h hLA ⟨ψ, hψ⟩ ha hk

end GlobalTheory.GenericAmpleDvr
