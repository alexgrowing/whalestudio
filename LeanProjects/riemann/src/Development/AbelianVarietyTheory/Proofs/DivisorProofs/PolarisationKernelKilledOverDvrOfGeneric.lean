import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerExt

theorem kernel_killed : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hab hpb hsq P P' hP hP' hPP' h1 h2 hsym hamp m hA T x hx
  obtain ⟨H, i, -, -, hflat, hker⟩ := GlobalTheory.T.finiteFlat_kernel_symmetric_birigidified_bundle W G hab P' hP' h1 h2 hsym hamp
  obtain ⟨y, rfl⟩ := (hker T x).1 hx
  have key : i ^ m = 1 := by
    haveI := hab.proper
    haveI : IsOpenImmersion (spMap (algebraMap W L)) := isOpenImmersion_spMap_of_isDiscreteValuationRing W L
    haveI : Nonempty (Sp L) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine GrpDense.hom_ext_of_points (spMap (algebraMap W L)) (fun T' t => ?_)
    obtain ⟨z, hz⟩ := GrpDense.pushPt_surjective hpb.1 T' (t ≫ i)
    have hzl : z.left ≫ φ = t.left ≫ i.left := congrArg (fun q => q.left) hz
    let F := (lift (snd G H ≫ i) (fst G H)).left
    obtain ⟨s, hs⟩ : ∃ s : (P'.pull F).Gen, s.IsGen := (hker H i).2 ⟨𝟙 H, Category.id_comp _⟩
    let c := (lift (snd A T' ≫ z) (fst A T')).left
    let q : Over.mk ((A ⊗ T').hom ≫ spMap (algebraMap W L)) ⟶ H :=
      Over.homMk ((snd A T').left ≫ t.left) (by
        simp only [Over.mk_hom, Category.assoc]
        rw [Over.w t]
        show (snd A T').left ≫ T'.hom ≫ _ = _
        rw [← Category.assoc, Over.w (snd A T')])
    let Ψ := (lift (pushPt hpb.1.w (fst A T')) q).left
    have hΨ1 : Ψ ≫ (fst G H).left = (fst A T').left ≫ φ := by rw [← Over.comp_left, lift_fst]; rfl
    have hΨ2 : Ψ ≫ (snd G H).left = (snd A T').left ≫ t.left := by rw [← Over.comp_left, lift_snd]; rfl
    have hF1 : F ≫ (fst G G).left = (snd G H).left ≫ i.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hF2 : F ≫ (snd G G).left = (fst G H).left := by rw [← Over.comp_left, lift_snd]
    have hc1 : c ≫ (fst A A).left = (snd A T').left ≫ z.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
    have hc2 : c ≫ (snd A A).left = (fst A T').left := by rw [← Over.comp_left, lift_snd]
    have hc : Ψ ≫ F = c ≫ φ₂ := by
      apply Over.tensorObj_ext
      · change (Ψ ≫ F) ≫ (fst G G).left = (c ≫ φ₂) ≫ (fst G G).left
        rw [Category.assoc, Category.assoc, hsq.1, hF1, ← Category.assoc, hΨ2, ← Category.assoc, hc1,
          Category.assoc, Category.assoc, hzl]
      · change (Ψ ≫ F) ≫ (snd G G).left = (c ≫ φ₂) ≫ (snd G G).left
        rw [Category.assoc, Category.assoc, hsq.2, hF2, hΨ1, ← Category.assoc, hc2]
    have e1 : LBIso (P.pull c) (P'.pull (Ψ ≫ F)) := GenSpread.lbIso_pull_of_lbIso hPP' c hc
    have e2 : LBIso (P'.pull (Ψ ≫ F)) ((P'.pull F).pull Ψ) := GenSpread.lbIso_pull_pull hP' Ψ rfl
    obtain ⟨s', hs'⟩ := RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP' F) Ψ) (pull_isLB hP' _) e2.symm
      (LB.genPull _ s Ψ) (LB.isGen_genPull _ s hs Ψ)
    have hzk := RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hP c) e1.symm s' hs'
    have hzm : z ^ m = 1 := hA T' z hzk
    rw [MonObj.comp_pow, MonObj.comp_one, ← hz]
    show pushHom hpb T' z ^ m = 1
    rw [← map_pow, hzm, map_one]
  rw [← MonObj.comp_pow, key, MonObj.comp_one]

end GlobalTheory.KerExt
