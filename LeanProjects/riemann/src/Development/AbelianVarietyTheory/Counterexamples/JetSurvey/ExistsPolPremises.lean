import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsEllipticCurveTwoAdic

noncomputable section

namespace GlobalTheory.BaseChangeToolsTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem both_hold : QkPullExistsSt ∧ PolOActPullSt := ⟨qkPullExists globalFns_holds, polOActPull⟩

section Pairs

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]

theorem injective_of_compat (hF : ArcPull.Compat φ F) : Function.Injective φ := fun a b h =>
  IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective
    ((hF a).trans (h ▸ (hF b).symm)))

theorem existsUnique_pair {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hF : ArcPull.Compat φ F) (k : ℕ)
    (p' : QkPt D' F k) : ∃! p : QkPt D F k, p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g := by
  obtain ⟨p, hp⟩ := both_hold.1 R R' φ D D' hD F hF k p'
  exact ⟨p, hp, fun q hq => TorusExt.qk_ext (hD.xe.symm.injective (hq.1.symm.trans hp.1))
    (ArcPull.pullGt_unique' hD hq.2 hp.2)⟩

theorem exists_premises (hF : ArcPull.Compat φ F) (D : DegPre R) (hB : D.TauBimult) (k : ℕ) (p : QkPt D F k) :
    ∃ (D' : DegPre R') (hD : IsPullDeg φ D D') (p' : QkPt D' F k),
      p'.y = hD.xe.symm p.y ∧ IsPullGtF φ hD F p.g p'.g := by
  obtain ⟨W, hW, hψ⟩ := PsiSpread.exists_psiOn D hB
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ (injective_of_compat hF))
    rw [this]; exact hW
  obtain ⟨w, hw, hs⟩ := ModelData.exists_strict D.P.isLB (pullback.fst D.P.A.hom (specOf φ))
  obtain ⟨D', hD, -⟩ := StrictPull.exists_isPullDeg_of_strict R R' φ D W hψ hgen (StrictPull.polPull D.P (specOf φ))
    (pullback.fst D.P.A.hom (specOf φ)) (isGrpPullback_pullback D.P.A (specOf φ)) w hw hs
  have hB' := tauBimult_of_isPullDeg globalFns_holds R R' φ D D' hD hB
  exact ⟨D', hD, ArcPull.pullQk hD globalFns_holds hF hB hB' p,
    (ArcPull.eq_pullQk_iff hD globalFns_holds hF hB hB' p _).1 rfl⟩

end Pairs

open PhiPowerTest in

theorem halfPeriod_instance : ∃ (D' : DegPre InhTate.R) (hD : IsPullDeg (RingHom.id _) multData.toPre D')
    (p' : QkPt D' KK 2), p'.y ≠ 0 ∧ ∀ p : QkPt multData.toPre KK 2,
      (p'.y = hD.xe.symm p.y ∧ IsPullGtF (RingHom.id _) hD KK p.g p'.g) ↔ p = halfPeriod := by
  have hF : ArcPull.Compat (RingHom.id InhTate.R) KK := fun _ => rfl
  obtain ⟨D', hD, p', h⟩ := exists_premises hF multData.toPre multData.tau_bimult 2 halfPeriod
  refine ⟨D', hD, p', fun h0 => ?_, fun p => ⟨fun hp => (existsUnique_pair hD hF 2 p').unique hp h, fun e => e ▸ h⟩⟩
  have e : halfPeriod.y = 0 := hD.xe.symm.injective ((h.1.symm.trans h0).trans (map_zero _).symm)
  exact one_ne_zero (show (1 : ℤ) = 0 from e)

theorem act_unique {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P' : PolAV S'} {g : P'.A.left ⟶ P.A.left}
    (hg : IsGrpPullback P'.A P.A f g) {O : Type} [CommRing O] [StarRing O] (o : P.OAct O) (o₁ o₂ : P'.OAct O)
    (h₁ : ∀ a, (o₁.act a).left ≫ g = g ≫ (o.act a).left) (h₂ : ∀ a, (o₂.act a).left ≫ g = g ≫ (o.act a).left) :
    o₁ = o₂ := by
  have e : o₁.act = o₂.act := funext fun a => Over.OverMorphism.ext
    (hg.1.hom_ext ((h₁ a).trans (h₂ a).symm) (by rw [Over.w, Over.w]))
  obtain ⟨⟨a₁, _, _, _, _⟩, _⟩ := o₁
  obtain ⟨⟨a₂, _, _, _, _⟩, _⟩ := o₂
  dsimp only at e
  subst e
  rfl

theorem exists_pol_premises {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (g : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f g ∧ LBIso (P.L.pull g) P'.L :=
  ⟨StrictPull.polPull P f, pullback.fst P.A.hom f, rfl, isGrpPullback_pullback P.A f,
    PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩

theorem elliptic_instance {R : Type} [CommRing R] [IsNoetherianRing R] (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    {S' : Scheme.{0}} (f : S' ⟶ Spec (CommRingCat.of R)) :
    ∃ (o : (WeierstrassCurve.ellPolAV W).OAct ℤ) (P' : PolAV S')
      (g : P'.A.left ⟶ (WeierstrassCurve.ellPolAV W).A.left),
      (∀ a : ℤ, o.act a = (𝟙 (WeierstrassCurve.ellPolAV W).A : _ ⟶ _) ^ a) ∧ P'.g = 1 ∧
      IsGrpPullback P'.A (WeierstrassCurve.ellPolAV W).A f g ∧ LBIso ((WeierstrassCurve.ellPolAV W).L.pull g) P'.L ∧
      ∃! o' : P'.OAct ℤ, ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  obtain ⟨o, ho⟩ := exists_oAct_int UU.SettingConsistentExample.cubeSt' _ (WeierstrassCurve.ellPolAV W)
  obtain ⟨P', g, hd, hg, hL⟩ := exists_pol_premises f (WeierstrassCurve.ellPolAV W)
  obtain ⟨o', ho'⟩ := both_hold.2 _ _ f _ P' g hg hL ℤ o
  exact ⟨o, P', g, ho, hd, hg, hL, o', ho', fun o₁ h₁ => act_unique hg o o₁ o' h₁ ho'⟩

end GlobalTheory.BaseChangeToolsTest

end
