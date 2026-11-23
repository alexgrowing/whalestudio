import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase

namespace PositivityTheory.HtPt.Pquo

section BaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UU

theorem exists_tq_baseChange_over : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F →
    ∀ Q : TQ G X, ∃ (Q' : TQ G' X) (p : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f p ∧
      Q'.q.left ≫ p = F ≫ Q.q.left := by
  intro S S' f X _ G _ G' _ F hF Q
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hF.1 Q.i
  have := Q.i_hom
  have := Q.q_hom
  have hA := Q.isAb
  let B' : Over S' := (Over.pullback f).obj Q.B
  let p : B'.left ⟶ Q.B.left := pullback.fst Q.B.hom f
  have hB : IsGrpPullback B' Q.B f p := isGrpPullback_pullback Q.B f
  have w : (F ≫ Q.q.left) ≫ Q.B.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ B' := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ Q.q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left Q.q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  have hAb : IsAbelianScheme B' := by
    have := hA.comm
    have := hA.smooth
    have := hA.proper
    have := hA.geomConnected
    exact
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd Q.B.hom f); infer_instance
        proper := by change IsProper (pullback.snd Q.B.hom f); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd Q.B.hom f); infer_instance }
  have ker : IsPullback i' (toUnit _) q' (η[B']) := by
    have k₀ : IsPullback Q.i.left (splitTorus S X).hom Q.q.left (η[Q.B]).left := by
      have := Q.isKernel.map (Over.forget S)
      rw [← Rosenlicht.toUnit_left]
      exact this
    have k₁ := (SplitTorus.isPullback_bcMap f X).paste_horiz k₀
    have e₁ : SplitTorus.bcMap f X ≫ Q.i.left = i'.left ≫ F := torusCompat_iff.1 hi
    have e₂ := eSec_comp_of_isGrpPullback hB
    have w' : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[B']).left := by
      refine hB.1.hom_ext ?_ ?_
      · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
        exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
        exact (Category.comp_id _).symm
    rw [e₁] at k₁
    have k₂ : IsPullback i'.left (splitTorus S' X).hom q'.left (η[B']).left :=
      IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp) (by simpa using e₂.symm)) w' sq
    rw [← Rosenlicht.toUnit_left] at k₂ w'
    exact IsPullback.of_map (Over.forget S') (Over.OverMorphism.ext w') k₂
  refine ⟨{ B := B'
            comm := hAb.comm
            isAb := hAb
            q := q'
            i := i'
            q_hom := isMonHom_of_over_isMonHom hF hB Q.q q' hq
            i_hom := hi.isMonHom hF
            q_flat := MorphismProperty.of_isPullback (P := @Flat) sq Q.q_flat
            q_surj := MorphismProperty.of_isPullback (P := @Surjective) sq Q.q_surj
            q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback sq Q.q_affine
            isKernel := ker
            loc := fun b χ => ?_ }, p, hB, hq⟩
  obtain ⟨V, hb, u, hu⟩ := Q.loc (p b) χ
  have hV : q'.left ⁻¹ᵁ p ⁻¹ᵁ V ≤ F ⁻¹ᵁ Q.q.left ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hq, Scheme.Hom.comp_preimage]
  exact ⟨p ⁻¹ᵁ V, hb, Units.map (F.appLE _ _ hV).hom.toMonoidHom u, hu.pull hF hi hV⟩

end BaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

attribute [local instance] SplitExt.free SplitExt.finite in

theorem fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (Pu : PELUnif (IsLocalRing.maximalIdeal V) tV) (P : AbPart tV (spMap r)), ∃ (Q : Out.PolAV (Sp ℂ)) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (T : GlobalTheory.UU.TQ P.tK.G X) (β : T.B ≅ Q.A), IsMonHom β.hom ∧ LBIso P.tK.PP.L (Q.L.pull (T.q ≫ β.hom).left) := by
  intro E _ _ _ H V _ _ _ r tV _ hk Pu P
  obtain ⟨s, hs⟩ : ∃ s : V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1) →+* ℂ,
      s.comp (Ideal.Quotient.mk _) = r :=
    ⟨Ideal.Quotient.lift _ r fun a ha => by
      rw [zero_add, pow_one, ← hk] at ha
      exact ha, RingHom.ext fun _ => rfl⟩
  have e : spMap s ≫ Out.thick V (IsLocalRing.maximalIdeal V) 0 = spMap r := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hs]
  obtain ⟨Ex, -, d, π, hπ, hd, -⟩ := GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord V _ Pu.D.toPre 0 tV.G (Pu.U.gt 0)
  have hG := isGrpPullback_pullback tV.G (Out.thick V (IsLocalRing.maximalIdeal V) 0)
  have w : P.m.φ ≫ tV.G.hom = (P.tK.G.hom ≫ spMap s) ≫ Out.thick V (IsLocalRing.maximalIdeal V) 0 := by
    rw [Category.assoc, e]
    exact P.m.cart.1.w
  obtain ⟨F, hF₁, hF₂⟩ : ∃ F : P.tK.G.left ⟶ (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G).left,
      F ≫ pullback.fst tV.G.hom (Out.thick V (IsLocalRing.maximalIdeal V) 0) = P.m.φ ∧
      F ≫ (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G).hom = P.tK.G.hom ≫ spMap s :=
    ⟨hG.1.lift _ _ w, hG.1.lift_fst _ _ w, hG.1.lift_snd _ _ w⟩
  have hF : IsGrpPullback P.tK.G (Out.thickObj V (IsLocalRing.maximalIdeal V) 0 tV.G) (spMap s) F :=
    IsGrpPullback.cancel hG (P.m.cart.congr e.symm hF₁.symm) hF₂
  obtain ⟨T, p, hp, hq⟩ := exists_tq_baseChange_over _ _ _ _ _ _ _ hF (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨Q, φ, -, hφ, hQ⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap r) Pu.D.toPre.P
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso ((IsGrpPullback.comp hp hπ).congr e rfl) hφ
  refine ⟨Q, Ex.X, inferInstance, inferInstance, inferInstance, T, β, hβ, ?_⟩
  have hc : (T.q ≫ β.hom).left ≫ φ = F ≫ (Pu.U.gt 0).pG.left := by
    rw [Over.comp_left, Category.assoc, hβ', ← hd]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) hq).trans (Category.assoc _ _ _))
  have h₁ : LBIso P.tK.PP.L (tV.PP.L.pull P.m.φ) := GlobalTheory.LN.GenericPoint.lbIso_of_sabMap P.m
  have h₂ : LBIso (Pu.U.LG.L.pull P.m.φ) (Pu.D.toPre.P.L.pull ((T.q ≫ β.hom).left ≫ φ)) :=
    LBIso.chartPull (chartPullSame Pu.U.LG.L _ _ _ F fun _ => hF₁.symm)
      (chartPullSame Pu.D.toPre.P.L _ _ _ F fun _ => hc) ⟨Pu.U.w 0, Pu.U.w_gen 0⟩
  rw [Pu.bundle] at h₂
  have h₃ : LBIso (Q.L.pull (T.q ≫ β.hom).left) (Pu.D.toPre.P.L.pull ((T.q ≫ β.hom).left ≫ φ)) :=
    GlobalTheory.LN.GenericPoint.lbIso_pull hQ _ rfl
  exact LBIso.trans P.tK.PP.isLB (pull_isLB tV.PP.isLB _) (pull_isLB Q.isLB _) h₁
    (LBIso.trans (pull_isLB tV.PP.isLB _) (pull_isLB Pu.D.toPre.P.isLB _) (pull_isLB Q.isLB _) h₂ h₃.symm)

end PositivityTheory.HtPt.Pquo
