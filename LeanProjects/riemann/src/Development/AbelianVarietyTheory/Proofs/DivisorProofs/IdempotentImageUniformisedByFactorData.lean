import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGroupActionStarAdjointBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageIsoUniformisedFactorOfAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationAlongGroupIsoLbIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.MumDesc

theorem image_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hi hp hip hpi
  obtain ⟨G₀, _, _, A₀, hG₀, ⟨U₀⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨ε, u, u', hε, hu, -, he, huu, hadj⟩ :=
    GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair R hR D D' F hF A' G' hG' U' oA oG hlin G hG inc pr hi hp hip hpi A₀ G₀ hG₀ U₀
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso R hR D A₀ G G₀ ε hε hG₀ U₀
  refine ⟨A₀, U, GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs _ G G' G₀ U.LG.L U'.LG.L U₀.LG.L U.LG.isLB U'.LG.isLB U₀.LG.isLB inc u u'
    (oG.act F.e) (oG.act (Star.star F.e)) (oG.act F.f) hi hu ?_ ?_ hadj
    (GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle R hR D' A' G' hG' U' F.O F.o oA oG hlin F.e) (he ▸ hU)⟩
  · rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  · rw [huu, oG.map_mul, oG.map_mul]

end GlobalTheory.MumDesc
