import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLoc
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section
namespace GlobalTheory.Mum

theorem isPullUnif_of_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D' : DegData R' (maximalIdeal R')) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → ∀ (A : PolAV (Sp (FractionRing R))) (D₁ : DegData R (maximalIdeal R)) (U₁ : Unif (maximalIdeal R) D₁ A G), LBIso U'.LG.L (U₁.LG.L.pull β) → ∃ (h : IsPullDeg ρ D₁.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf ρ)).obj G), bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = β ∧ IsPullUnif ρ h bc U₁ U' := by
  intro R _ _ _ hRb R' _ _ _ ρ hfin D' A' G' _ _ hsa' U' G _ _ β hsa hgp A D₁ U₁ hL
  obtain ⟨hR', hinj, hfinite⟩ := hfin
  have hR := hRb.1
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap ρ))
  subst hbc
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    GlobalTheory.ResidueGalois.map_maximalIdeal_le ρ hfinite.to_isIntegral
  have hP := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have sq : spMap (fracMap hinj) ≫ jK R = jK R' ≫ spMap ρ := (fracMap_sq hinj).symm.trans (Category.id_comp _)
  obtain ⟨A'', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hinj)) A
  have gpA : IsGrpPullback A''.A A.A (spMap (fracMap hinj)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U₁.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap hinj) ≫ jK R)
      (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (spMap ρ)) :=
    ((isGrpPullback_pullback G' (jK R')).comp hgp).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₁.gen.inv.left ≫ U₁.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A''.L.pull eA.hom.left) (U₁.LG.L.pull (pullback.fst G'.hom (jK R') ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf ρ))) := by
    refine LBIso.trans (pull_isLB A''.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U₁.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A''.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₁.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U₁.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₁.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U₁.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [← heA]; simp only [Category.assoc]
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ρ) = specOf ρ ≫ eSec G :=
    (cubeMapOf hgp).e_comm
  obtain ⟨w₀, hw₀⟩ := hL
  have hσ : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨wL, gL, pL⟩ := GlobalTheory.UnifPreCompare.exists_rigidified U₁.LG.isLB U'.LG.isLB G'.hom (eSec G') hσ w₀ hw₀
    U'.LG.rig U'.LG.rigGen U₁.LG.rig U₁.LG.rigGen (specOf ρ) he
  have mL : LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig
      (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) (specOf ρ) he U₁.LG.L U₁.LG.rig) :=
    (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U₁.LG.rig (specOf ρ) _
      (rigPull_le (G' := G') (G := G) _ (specOf ρ) he U₁.LG.L) (fun _ => rfl)).2 pL
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists R (maximalIdeal R) hR D₁
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D'', hD₁, U'', hLG, -, H₁⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds R R' (maximalIdeal R) (maximalIdeal R')
    hR hR' ρ hI D₁ A G hsa U₁ Wo hψ hgen G' bc mbc A'' dA eA mE wA U'.LG wL he gL mL
  obtain ⟨wL₀, g₀, m₀⟩ := exists_iso_of_eq hLG.symm
  have h6 := GlobalTheory.unifUniq GlobalTheory.abelianSchemeLaws_all.1.globalFns GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    GlobalTheory.abelianSchemeLaws_all.1.ample
  obtain ⟨hD₂, hlev, -⟩ := h6 R' (maximalIdeal R') hR' D'' D' A'' A' G' hsa' U'' U' wL₀ g₀ m₀
  have hs := specOf_id R'
  haveI mR : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨bc₀, -, hbc₀⟩ := grpPullback_iso ((isGrpPullback_of_iso (Iso.refl G')).congr hs.symm rfl)
    (isGrpPullback_pullback G' (Out.specOf (RingHom.id R')))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G'.hom (Out.specOf (RingHom.id R')) = 𝟙 _ := hbc₀
  have H₂ := isPullUnif_of_uniq U'' U' hD₂ wL₀ g₀ m₀ hlev bc₀ hbc₀'
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp hinj (fun _ _ h => h) hD₁ hD₂
  have hb : bc.hom.left ≫ pullback.fst G.hom (specOf ((RingHom.id R').comp ρ)) =
      (bc₀.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) ≫
        (bc.hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    rw [hbc₀', Category.id_comp]
  exact ⟨r, bc, rfl, GalMul.isPullUnif_comp r₁ r₂ r₃ T hb H₁ H₂⟩

end GlobalTheory.Mum
