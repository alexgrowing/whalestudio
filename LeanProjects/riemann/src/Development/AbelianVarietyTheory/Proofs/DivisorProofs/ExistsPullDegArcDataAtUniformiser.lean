import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsPullDegId
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionValuation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TraitArcMatch

open GlobalTheory.TraitArc GlobalTheory.TauTwist GlobalTheory.ArcBuild GlobalTheory.ArcOfPoint Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {T : CDVR}

theorem genRel_psi_twist (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : D.toPre.X) :
    GenRel (isoPullId (idIso D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 (H := H) D hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF D hϖ y y / 2 = qv D hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF D hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF D hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val D.toPre.P.isLB (DVR.pullGen_isGen _ _ _ _ (D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (TraitArc.tF D hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, TraitArc.tF, beF_w0 D oD, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv D hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (TraitArc.tF D hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

theorem exists_isPullDeg_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : Formalism.L2.Pj.CDVR) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X] (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) (ϖ : T.V) (hϖ : Irreducible ϖ) (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.TraitArc.beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A) (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : GlobalTheory.TraitArc.LieCl D oD Dm β b) (hTate : GlobalTheory.TraitArc.TateCl D oD hϖ Dm β b hdiv pA pM) (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp T.V ⟶ Y.X), Y.HasArcData (GlobalTheory.TraitArc.arc D oD hϖ β b hX hw hdiv pA pM hLie hTate) (maximalIdeal T.V) (RingHom.id T.V) ϖ y → ∃ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), Nonempty (IsPullDeg (RingHom.id T.V) D.toPre P.D.toPre) := by
  intro E _ _ _ H Dm l c O _ β T b D _ oD ϖ hϖ hX hw hdiv pA pM hLie hTate Xo Y y hY
  obtain ⟨t, m, P, φ, he, w, e, h1, h2, h3, -, h5, h6⟩ := hY
  refine ⟨t, m, P, ?_⟩
  have hid : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he0 : eSec D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec D.toPre.P.A := by
    rw [hid, Category.comp_id]; exact (Category.id_comp _).symm
  have p : IsGrpPullback D.toPre.P.A D.toPre.P.A (spMap (RingHom.id T.V)) (𝟙 _) := by
    have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
    exact (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr hid.symm rfl
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  let F := AlgebraicClosure (FractionRing T.V)
  have k6 := (h6 F (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) (fun _ => rfl) rfl).1
  have r := (maps_iff (idW D.toPre.P.L) _ (fun _ => eSec D.toPre.P.A) _ D.toPre.rig D.toPre.rig _ _
    (rigPull_le (𝟙 _) _ he0 D.toPre.P.L) (fun _ => rfl)).1 (maps_rig_id D.toPre he0)
  have r' := (maps_iff w _ (fun _ => eSec D.toPre.P.A) _ P.D.toPre.rig D.toPre.rig _ _
    (rigPull_le φ _ he D.toPre.P.L) (fun _ => rfl)).1 h3
  let xe : P.D.toPre.X ≃+ D.toPre.X := e.symm.toAddEquiv
  have hxe : ∀ y, xe (e y) = y := fun y => e.symm_apply_apply y
  obtain ⟨hD, -⟩ := GlobalTheory.ArcData.exists_isPullDeg_id D.toPre P.D.toPre (A₀ := D.toPre.P.A) (M₀ := D.toPre.P.L)
    D.toPre.P.isLB D.toPre.rig p h1 (idW D.toPre.P.L) w
    ((isGen_iff _).1 ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.toPre.P.isLB) rfl))) ((isGen_iff _).1 h2)
    r r' xe (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      refine (h5 y).trans ?_
      rw [hid, Category.id_comp, Category.comp_id, hxe]; rfl)
    Wo hWo ψW (jFK (R := T.V) F) (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hxe]
      exact ⟨_, _, _, genRel_psi_twist D oD hϖ F y, k6 y⟩)
  exact ⟨hD⟩

end GlobalTheory.TraitArcMatch
