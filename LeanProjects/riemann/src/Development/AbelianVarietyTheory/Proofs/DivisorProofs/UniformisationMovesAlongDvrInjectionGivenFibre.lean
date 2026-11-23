import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsTer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.UnifMoveGiven

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in

theorem exists_pull_given {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (gA : A'.A.left ⟶ A.A.left)
    (gpA : IsGrpPullback A'.A A.A (spMap gK) gA) (hL : LBIso A'.L (A.L.pull gA)) (dA : A'.g = A.g) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre)
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      (hL.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, U', hPU, by rw [hgenU]; exact heA⟩

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear GlobalTheory.UnifMove in

theorem move_given : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  intro V V' _ _ _ _ _ _ hV hV' φ φK hK hI D A G _ _ U A' ψ gp hL hg F _ _ _ hF
  have aV : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have aV' : AdmBase V' (IsLocalRing.maximalIdeal V') := ⟨inferInstance, inferInstance, inferInstance, hV'⟩
  have hK' : ∀ r, φK (algebraMap V _ r) = algebraMap V' _ (φ r) := fun r => RingHom.congr_fun hK r
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (φK.injective (by rw [hK', hK', h]))
  have sq : spMap φK ≫ jK V = jK V' ≫ spMap φ := by
    refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hK
  have hFc : ∀ r : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) r) =
      algebraMap (FractionRing V') F (algebraMap V' (FractionRing V') (φ r)) := fun r => by
    rw [← hK', ← hF]; rfl
  have sF : jFK (R := V') F ≫ spMap φK = jFK (R := V) F := by
    refine (Spec.map_comp _ _).symm.trans ?_
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hF
  obtain ⟨D', hD, U', hU, hgen⟩ := exists_pull_given aV aV' φ hφ hI φK sq
    (isSemiAbelian_of_unifPre_dvr V D A G U.toUnifPre) U A' ψ gp hL hg
  refine ⟨D', hD, _, inferInstance, inferInstance, U',
    isSemiAbelian_of_unifPre_dvr V' D' A' _ U'.toUnifPre, fun k hk q x H => ?_⟩
  obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 V V' φ D.toPre D'.toPre hD
    D.tau_bimult D'.tau_bimult F hFc k
  obtain ⟨hy, hg'⟩ := (hτ q _).1 rfl
  have w : x.left ≫ A.A.hom = jFK (R := V') F ≫ spMap φK := (Over.w x).trans sF.symm
  let x' : TFK (R := V') F ⟶ A'.A := Over.homMk (gp.1.lift x.left (jFK (R := V') F) w) (gp.1.lift_snd _ _ _)
  have hx : x'.left ≫ ψ = x.left := gp.1.lift_fst _ _ _
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  refine ⟨τ q, x', by rw [hy]; exact hD.xe.apply_symm_apply _, hx,
    qkToAk_baseChange abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.secBaseChange V V' _ _ aV aV' φ D A G U
      _ (Iso.refl _) mR A' D' hD U' hU F hFc k hk q x (τ q) x' hy hg' ?_ H⟩
  have n : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (spMap φ) := Category.id_comp _
  rw [hbc, ← hgen, ← Category.assoc U'.gen.inv.left, n, Category.id_comp, ← Category.assoc, hx]

end GlobalTheory.UnifMoveGiven

end
