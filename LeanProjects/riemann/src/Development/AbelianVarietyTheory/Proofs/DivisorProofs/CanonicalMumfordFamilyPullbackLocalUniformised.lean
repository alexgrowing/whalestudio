import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedFactorAlgebraicPartPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordPairingRetractBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonPull

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

end GlobalTheory.Mum.CanonPull

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.canon_pull_unif : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)
:= by
  intro R V' _ _ _ _ _ _ θ hR hV hθ Q W G₁ _ _ P hG hC hW D' ex hP
  obtain ⟨hPl, D₀, F, A₀, G₀, i₀, c₀, U₀, oA, oG, inc, pr, hψ, hG₀, lin, mi, mp, hip, hpi, hL⟩ := hC
  have bR : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have bV : Base V' := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  obtain ⟨D₁, hD, A₁, U₁, m, o₁, oA₁, oG₁, hL₁, hx, ho, ha, lin₁⟩ :=
    GlobalTheory.T.linearUniformisation_pullback_localHom R V' θ bR bV hθ D₀ A₀ G₀ hG₀ U₀ F.O F.o oA oG lin W hψ hW
  obtain ⟨β, gβ, hc, H⟩ := GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex hP
  obtain ⟨inc', pr', xi, xp, h₁, h₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉⟩ :=
    GlobalTheory.T.polarisedFactor_algebraic_part_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex β gβ hc
  obtain ⟨w, hw, hτ⟩ := H inc' xi h₁ h₂ b₇
  let F₁ : Factor D'.toPre D₁.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := hw,
      tau := fun a b z J J' hJ hJ' =>
        ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').symm.trans (hτ a b z J J' hJ hJ') }
  obtain ⟨π₂, sq, hl⟩ := GlobalTheory.T.mumfordPairingRetract_baseChange _ _ (specOf θ) G₁ G₀ inc (oG.act F.f) U₀.LG.L U₁.LG.L P U₀.LG.isLB U₁.LG.isLB hPl hL₁ hL
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data V' bV D' D₁ F₁ F.alg A₁ _ (IsSemiAbelian.pullback _ G₀ hG₀) U₁ oA₁ oG₁ lin₁
    ((Over.pullback (specOf θ)).obj G₁) (IsSemiAbelian.pullback _ G₁ hG) ((Over.pullback (specOf θ)).map inc)
    ((Over.pullback (specOf θ)).map pr) inferInstance inferInstance
    (by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])
    (by rw [← CategoryTheory.Functor.map_comp, hpi]; exact (ha _).symm)
  refine ⟨(Over.pullback (specOf θ)).obj G₁, inferInstance, inferInstance, _, π₂, A, U, isGrpPullback_pullback G₁ (specOf θ), sq, ?_⟩
  rw [show oG₁.act F₁.f = (Over.pullback (specOf θ)).map (oG.act F.f) from ha _] at hU
  exact LBIso.trans (GlobalTheory.Mum.CanonPull.lam_isLB _ U.LG.isLB)
    (pull_isLB (GlobalTheory.Mum.CanonPull.lam_isLB _ U₁.LG.isLB) _) (pull_isLB hPl _) hU hl
