import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmple

theorem exists_relAmple (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W))
    [GrpObj G] (hG : IsAbelianScheme G) : ∃ L : LB G.left, L.IsLB ∧ Out.RelAmple G L := by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec G (IsLocalRing.closedPoint W)) trivial
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine W G hG V hV fun s => ⟨eSec G s, ?_, ?_⟩
  · have hsp : (s : PrimeSpectrum W) ⤳ IsLocalRing.closedPoint W :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal s.2.ne_top)
    exact (hsp.map (eSec G).continuous).mem_open V.isOpen hx
  · rw [← Scheme.Hom.comp_apply, he]
    rfl

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem exists_generating_sq (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K']
    [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left)
    (hN : N.IsLB) (σ : (N.pull (pullback.fst G.hom (spMap (algebraMap W K')))).Sec) (hσ : ∃ j, σ.f j ≠ 0) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw N 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hK := IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))
  have hk := IsPullback.of_hasPullback G.hom (spMap (IsLocalRing.residue W))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hk
  obtain ⟨-, ⟨t, -, a, x, hx, hxa⟩, -⟩ := GlobalTheory.DvrModel.existsUnique_zpow_mul_sec hK hk hϖ hN σ hσ
  let F := AlgebraicClosure K'
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K' F).comp (algebraMap W K'))
  let g : W →+* O := ((algebraMap K' F).comp (algebraMap W K')).codRestrict O.toSubring hO
  have : IsLocalHom g := hloc
  have hg : Function.Injective g := fun a b e =>
    IsFractionRing.injective W K' ((algebraMap K' F).injective (congrArg Subtype.val e))
  have hflat : g.Flat := by
    letI := g.toAlgebra
    have : Module.IsTorsionFree W O := Module.isTorsionFree_iff_algebraMap_injective.2 hg
    exact (inferInstance : Module.Flat W O)
  have : Surjective (spMap g) := by
    letI := g.toAlgebra
    have : Module.Flat W O := hflat
    have : IsLocalHom (algebraMap W O) := ‹_›
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := O)
    exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩
  let B : Over (Sp O) := (Over.pullback (spMap g)).obj G
  let π : B.left ⟶ G.left := pullback.fst G.hom (spMap g)
  have h : IsGrpPullback B G (spMap g) π := isGrpPullback_pullback G _
  have hB := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h
  have := hB.comm
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  have hr : Out.Rigidified G N := DVR.exists_gen_of_isLB_local (V := W) _ (pull_isLB hN _)
  obtain ⟨R, hR, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.allSixLaws.1 _ G hG N hN hr
    (GlobalTheory.GenericAmpleDvr.triv_theta hG hN)
  subst hR
  obtain ⟨hLB, hr', ⟨c', -⟩, -⟩ := Out.CubePf.cubePull _ _ G B (cubeMapOf h) R c
  have cube : GlobalTheory.AbLaw.Triv (Theta B (R.L.pull π)) := ⟨c'.t, c'.isGen⟩
  obtain ⟨⟨t', ht', -⟩, H⟩ := GlobalTheory.SecPullIso.section_pull _ _ π _ _ _ hN (pull_isLB hN π)
    (Out.CubePf.idIsoL_isGen (pull_isLB hN π)) t
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap g) x
    (IsLocalRing.closedPoint O) (hx.trans (IsLocalRing.comap_closedPoint g).symm)
  have hmem : z ∈ Out.nonzeroLocus t' := by
    rw [H t' ht']
    exact (congrArg (· ∈ Out.nonzeroLocus t) hz₁).mpr (TopologicalSpace.Opens.mem_iSup.2 ⟨a, hxa⟩)
  have hu := GlobalTheory.SquareGenerated.exists_secs_sq_generate O F B hB _ (pull_isLB hN π) cube t' ⟨z, hmem, hz₂⟩
  rw [← GlobalTheory.AmpleCrit.pull_pw_eq] at hu
  obtain ⟨m, u, hu⟩ := hu
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  exact GlobalTheory.AmpleCrit.exists_cover_of_pull g hflat G.hom π B.hom h.1 (GlobalTheory.AbLaw.isLB_pw hN _) u hu

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem veryAmpleBy_pw_of_generic : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s → M.IsLB → w.IsGen → ∃ n : ℕ, 1 ≤ n ∧ ∃ (m' : ℕ) (t : Fin (m' + 1) → (GlobalTheory.AbLaw.pw M n).Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom (GlobalTheory.AbLaw.pw M n) t := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s M w hH hva hM hw
  have := hG.proper
  have := hA.proper
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have : IsProper (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))) ‹IsProper G.hom›
  have hHa : Out.RelAmple A H := GlobalTheory.MulFiniteAny.relAmple_of_veryAmpleBy' hH s hva
  have sq : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    have h1 : IsPullback e.hom.left (pullback.snd G.hom (spMap (algebraMap W K')))
        (pullback.snd A.hom (spMap (algebraMap K K'))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simpa using Over.w e.hom⟩
    simpa using h1.paste_horiz (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K')))
  have hHK := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hH hHa sq
  have hMK : Out.RelAmple (Over.mk (pullback.snd G.hom (spMap (algebraMap W K'))))
      (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) := by
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hH _)] at hHK
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)]
    exact (GlobalTheory.isAmpleLB_congr (pull_isLB hM _) (pull_isLB hH _) ⟨w, hw⟩).2 hHK
  obtain ⟨L, hL, hLa⟩ := exists_relAmple W G hG
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  have hne : Nonempty (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).left :=
    ⟨pullback.lift (spMap (algebraMap W K') ≫ eSec G) (𝟙 _) (by rw [Category.assoc, he]; simp)
      (IsLocalRing.closedPoint K')⟩
  obtain ⟨a, σ, ha, hσ⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K'
    (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))) (L.pull (pullback.fst G.hom (spMap (algebraMap W K'))))
    (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) inferInstance hne (pull_isLB hL _) (pull_isLB hM _) hMK
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div hp hL
  obtain ⟨σ', hσ'⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN _)
    (LB.isLB_div (LB.isLB_linComb (pull_isLB hM _) _ _) (pull_isLB hL _))
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst G.hom (spMap (algebraMap W K'))) a) ⟨σ, hσ⟩
  obtain ⟨r, u, hu⟩ := exists_generating_sq W K' G hG _ hN σ' hσ'
  have hiso : LBIso (lbPow (LB.div (lbPow M a) L) 2) (GlobalTheory.AbLaw.pw (LB.div (lbPow M a) L) 2) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow hN 2) (GlobalTheory.AbLaw.isLB_pw hN 2)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hN, GlobalTheory.AmpleStabFinite.cls_pw hN]
    first
      | rfl
      | exact (natCast_zsmul _ 2).symm
      | exact natCast_zsmul _ 2
      | simp only [two_smul, two_nsmul]
      | (simp; done)
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2)
    (GlobalTheory.AbLaw.isLB_pw hN _) hiso (u i)
  have hcov : ⨆ i, Out.nonzeroLocus (v i) = ⊤ := by
    simp_rw [hv]
    exact hu
  have hLamp := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hL).1 hLa
  have hMa := (GlobalTheory.isAmpleLB_pow_iff hM ha).1 (hLamp.of_pow_div_generated hp (by norm_num) v hcov)
  have hMrel := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hM).2 hMa
  obtain ⟨n, hn, m', t, -, ht⟩ := GlobalTheory.AbLaw.veryAmpleBy_of_relAmple hM hMrel (𝟙 G.left) (Category.id_comp _) hM
    (GlobalTheory.lbIso_pull_id hM).symm
  exact ⟨n, hn, m', t, ht⟩

end GlobalTheory.ModelAmple
