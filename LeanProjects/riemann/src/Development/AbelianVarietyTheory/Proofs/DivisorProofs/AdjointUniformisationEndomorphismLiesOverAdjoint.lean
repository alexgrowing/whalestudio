import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBalaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := GlobalTheory.T.rosatiAdjoint_unique_degenerationData

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
