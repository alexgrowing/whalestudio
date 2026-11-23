import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationDataStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.NoTorus

theorem pmaps_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    PMaps (isoPullId (Geo.Tor.idIso L) hF) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  subst hF
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id]
  refine (gen_trans ht r z (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)).trans
    (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  rw [gw_isoPullId (Geo.Tor.idIso L) rfl (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]
  rfl

theorem nonempty_isPullDeg_self {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    (D : DegData R I) : Nonempty (IsPullDeg (RingHom.id R) D.toPre D.toPre) := by
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  exact ⟨hD⟩

end GlobalTheory.NoTorus

namespace GlobalTheory

theorem isAbelianScheme_of_unif_of_subsingleton : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (IsLocalRing.maximalIdeal V) D A G → Subsingleton D.toPre.X → IsAbelianScheme G := by
  intro hL hL₂ V _ _ _ _ hc D A G _ hG hsa U hX
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨A', eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) D.toPre.P
  obtain ⟨hD⟩ := NoTorus.nonempty_isPullDeg_self hR D
  obtain ⟨ψ, -⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ V _ hR rfl D D A A' G D.toPre.P.A hsa
    (isSemiAbelian_of_isAbelianScheme _ D.toPre.P.isAb) U
    ⟨SelfUnif.selfPre D A' eA hA hw, fun k _ =>
      SelfUnif.expBij D A' eA hA hw hL.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩ hD
  have e : G.hom = ψ.inv.left ≫ D.toPre.P.A.hom := (Over.w ψ.inv).symm
  have := D.toPre.P.isAb.proper
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  exact ⟨hG, hsa.smooth, by rw [e]; infer_instance, hsa.geomConnected⟩

end GlobalTheory

end
