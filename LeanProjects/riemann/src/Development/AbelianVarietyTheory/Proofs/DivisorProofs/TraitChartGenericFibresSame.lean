import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifPullbackOfCanonicalOnStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem sameFib_trait_chart : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  intro g n φ F C G₁ _ _ P hP hC T V' _ _ _ θ f fK hV' hθ hs hfK D' e hDF G' _ _ πG A' U' hU
  obtain ⟨G'', _, _, π, π₂, A'', U'', hπ, hπ₂, hΛ''⟩ := GlobalTheory.T.unif_pullback_of_canonical_on C G₁ P hP hC V' θ hV' hθ hs D' e hDF
  obtain ⟨hG', κ, πK, α, α₂, hκ, -, hα, hα₂, hΛ', -⟩ := hU

  have hκ' : κ = spMap fK := by
    haveI := GlobalTheory.Mum.EvenDesc.mono_jK T.V
    rw [← cancel_mono (jK T.V), hκ]
    have e₁ : (algebraMap V' (FractionRing V')).comp f = fK.comp (algebraMap T.V (FractionRing T.V)) :=
      RingHom.ext fun a => (hfK a).symm
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) e₁
  subst hκ'
  have hsG'' : IsSemiAbelian G'' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hP.2.2.1
  have hsG' : IsSemiAbelian G' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hG' T.semi
  have hAdm : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  obtain ⟨hD, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self V' _ hAdm D'
  obtain ⟨ψ, hψm, hψL, -⟩ := GlobalTheory.exists_generic_iso_of_unif GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 V'
    (maximalIdeal V') hAdm (maximalIdeal.isMaximal V').ne_top D' D' A'' A' G'' G' hsG'' hsG' U'' U' hD
  haveI := hψm
  haveI := U''.gen_hom
  haveI : IsMonHom U''.gen.symm.hom := inferInstanceAs (IsMonHom U''.gen.inv)

  let b : A'.A.left ⟶ G''.left := ψ.hom.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (jK V')
  have hb : IsGrpPullback A'.A G'' (jK V') b :=
    ((isGrpPullback_of_iso ψ).comp ((isGrpPullback_of_iso U''.gen.symm).comp
      (isGrpPullback_pullback G'' (jK V')))).congr (by simp only [Category.id_comp]) rfl
  obtain ⟨b₂, hb₂, hΛb⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (jK V') G'' A'.A b hb
  have hPLB : P.IsLB := hP.2.2.2.1.1
  have hL : LBIso A'.L (U''.LG.L.pull b) :=
    LBIso.trans A'.isLB (pull_isLB A''.isLB _) (pull_isLB U''.LG.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp (ψ.hom.left ≫ U''.gen.inv.left)
        (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
        (by simp only [b, Category.assoc]) U''.ext)
  have hΛA : LBIso (abelian₂ A'.A A'.L) (P.pull (b₂ ≫ π₂)) :=
    hΛb U''.LG.L A'.L _ P π₂ U''.LG.isLB A'.isLB hPLB hL hΛ''
  have hθK : spMap ((algebraMap V' (FractionRing V')).comp θ) = jK V' ≫ spMap θ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  refine ⟨A'.A, inferInstance, inferInstance, α, α₂, b ≫ π, b₂ ≫ π₂, hα, hα₂,
    (hb.comp hπ).congr hθK.symm rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hπ₂.1, ← Category.assoc, hb₂.1, Category.assoc]
  · rw [Category.assoc, hπ₂.2, ← Category.assoc, hb₂.2, Category.assoc]
  · exact LBIso.trans (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hPLB _) hΛ'.symm hΛA

end GlobalTheory.TChart
