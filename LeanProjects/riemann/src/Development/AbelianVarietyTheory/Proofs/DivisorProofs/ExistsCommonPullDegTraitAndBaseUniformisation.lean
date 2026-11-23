import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SixthLawsAndUnifUniq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CommonPull

open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_rig_iso_of_eq {S : Scheme.{0}} {H : Over S} [GrpObj H] (L₁ L₂ : RigLB H) (h : L₁ = L₂) :
    ∃ w : LB.Iso L₂.L L₁.L, w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec H) (fun _ => 1)) L₂.rig L₁.rig := by
  subst h
  exact ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso L₁.L, idIso_isGen L₁.isLB, fun p => L₁.rigGen p.1 p.2⟩

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  intro R _ _ _ hR D G _ _ L _ hG hT D₂ A U₂ hL
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφ, hloc, hβ, hLβ, hD⟩ := hT
  subst hL
  obtain ⟨hLw, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have h6 := GlobalTheory.sixthLaws_and_unifUniq.2
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G (spMap φ))
  haveI := mbc
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)

  have sq : spMap (fracMap hφ) ≫ jK R = jK W ≫ spMap φ := (fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hLw.polBaseChange _ _ (spMap (fracMap hφ)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₂.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj G') G (spMap (fracMap hφ) ≫ jK R)
      (pullback.fst G'.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback G' (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₂.gen.inv.left ≫ U₂.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₂.LG.L.pull (pullback.fst G'.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₂.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₂.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₂.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₂.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₂.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · show pullback.fst G'.hom (jK W) ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
      rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G := by
    show eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (spMap φ) = _
    rw [hbc]; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, gwL, rwL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G G'
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) he U₂.LG U'.LG (by
      show ∃ w : LB.Iso U'.LG.L (U₂.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (spMap φ))), w.IsGen
      rw [hbc]; exact hLβ)
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R (maximalIdeal R) hR.1 D₂
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo
  obtain ⟨D₂', hD₂, U₂', hLG, -, -⟩ := h4.unifBaseChange R W (maximalIdeal R) (maximalIdeal W) hR.1 hW' φ
    (map_maximalIdeal_le φ) D₂ A G hG U₂ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gwL rwL
  obtain ⟨wU, gU, rU⟩ := exists_rig_iso_of_eq U₂'.LG U'.LG hLG
  obtain ⟨hU, -⟩ := h6 W (maximalIdeal W) hW' D₂' D' A'' A' G' hG' U₂' U' wU gU rU
  obtain ⟨hD'⟩ := hD
  refine ⟨W, inferInstance, inferInstance, φ, D'.toPre, hφ, ⟨hD'⟩, ?_⟩
  exact RingHom.id_comp φ ▸ GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ Function.injective_id hD₂ hU

end GlobalTheory.Mum.CommonPull
