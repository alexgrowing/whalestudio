import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfTriv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmpleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecPullNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVRStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.GoodPol

section General

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem eq_one_of_inK (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (hk : Out.KTriv A' L') {Z : Scheme.{0}} (q : Z ⟶ S') {t : Z ⟶ S} (ht : t = q ≫ f) (x : Over.mk t ⟶ A)
    (hx : InK A L x) : x = 1 := by
  subst ht
  let y : Over.mk q ⟶ A' := Over.homMk (h.1.lift _ _ (Over.w x)) (h.1.lift_snd _ _ _)
  have hy : pushPt h.1.w y = x := Over.OverMorphism.ext (h.1.lift_fst _ _ (Over.w x))
  have e : y = 1 := (inK_of_push h hL hL' hw y (hy ▸ hx)).eq_one hk
  exact hy.symm.trans ((congrArg (pushHom h (Over.mk q)) e).trans (map_one _))

theorem inK_of_triv {T : Over S} {x : T ⟶ A} (hx : Triv (Out.translDiff A L x)) : InK A L x := fun _ =>
  ⟨⊤, trivial, hx.elim fun c hc => gen_chartPull (Geo.Tor.chartPullPull _ _ _ rfl) c hc⟩

theorem triv_theta_pw [IsCommMonObj A] (hL : L.IsLB) (h : Triv (Theta A L)) (d : ℤ) : Triv (Theta A (pw L d)) := by
  have h₁ := (CechPic.cls_eq_zero_iff (TripleExt.isLB_cube (x3 A) hL)).2 h
  refine (CechPic.cls_eq_zero_iff (TripleExt.isLB_cube (x3 A) (isLB_pw hL d))).1 ?_
  rw [TripleExt.cls_cube _ hL] at h₁
  rw [TripleExt.cls_cube _ (isLB_pw hL d), AmpleStabFinite.cls_pw hL]
  unfold TripleExt.cubeCls at h₁ ⊢
  simp only [map_zsmul, smul_comm _ d, ← Finset.smul_sum]
  rw [h₁, smul_zero]

theorem exists_ne_zero {X Y : Scheme.{0}} (π : Y ⟶ X) (y : Y) {N : LB X} (hN : N.IsLB) {I : Type}
    (s : I → LB.Sec N) (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec (N.pull π)) (k : _), σ.f k ≠ 0 := by
  have hx : π y ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨⟨σ, hσ, -⟩, H⟩ := SecPullIso.section_pull X Y π N _ _ hN (pull_isLB hN π)
    (Out.CubePf.idIsoL_isGen (pull_isLB hN π)) (s i)
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ Out.nonzeroLocus σ by rw [H σ hσ]; exact hi)
  refine ⟨σ, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

end General

section DVR

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Over (Sp V)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L' : LB A'.left}

theorem kTriv_of_generic (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (c : CubicalStr A L)
    (ha : Out.RelAmple A L.L) (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ) (hL' : L'.IsLB)
    (hw : LBIso L' (L.L.pull φ)) (hk : Out.KTriv A' L') : Out.KTriv A L.L := by
  have hL := L.isLB
  obtain ⟨d, -, n, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy V A L.L hL).1 ha
  have hP : IsProjBy A.hom := ⟨_, isLB_pw hL _, n, s, hs⟩
  obtain ⟨hO, hu, hK⟩ := TrivTwist.inK_iff_trivial_twist _ A L.L hL
  obtain ⟨Z, i, hi, hZ⟩ := TwistKer.exists_closed_twist_kernel hG V A hA hP L.L (pw L.L 0) hL hO
  have hfin : IsFinite Z.hom := AmpleStabFinite.isFinite_of_relAmple hG V A hA L.L (pw L.L 0) hL hO ha Z i hi hZ
  have hflat : Flat Z.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hG V A hA hP L c (pw L.L 0) hO hu Z i hi hZ hfin
  have hrep : ∀ (T : Over (Sp V)) (x : T ⟶ A), InK A L.L x ↔ ∃ y : T ⟶ Z, y ≫ i = x :=
    fun T x => (hK _ rfl T x).trans (hZ T x)
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let z : Over.mk (pullback.snd Z.hom (spMap (algebraMap V K)) ≫ spMap (algebraMap V K)) ⟶ Z :=
    Over.homMk (pullback.fst _ _) pullback.condition
  have hz : z ≫ i = z ≫ 1 :=
    (eq_one_of_inK h hL hL' hw hk _ rfl _ ((hrep _ _).2 ⟨z, rfl⟩)).trans (MonObj.comp_one _).symm
  have hi1 : i = 1 := over_ext_of_schemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K)))
    (congrArg (fun q => q.left) hz)
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  rw [hi1, MonObj.comp_one]

theorem exists_generating (hA : IsAbelianScheme A) (c : CubicalStr A L) (O F : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field F] [IsAlgClosed F] [Algebra O F] [IsFractionRing O F] (g : V →+* O) [IsLocalHom g]
    (hg : Function.Injective g)
    (ha : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap V K))))
      (L.L.pull (pullback.fst A.hom (spMap (algebraMap V K))))) :
    ∃ (d m : ℕ) (u : Fin (m + 1) → LB.Sec (pw L.L d)), 1 ≤ d ∧ ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hL := L.isLB
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ A
  obtain ⟨d, hd, n, s, hs, -⟩ := (Unif.relAmple_iff_veryAmpleBy K _ _ (pull_isLB hL _)).1 ha
  have hH := isLB_pw hL d
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback A.hom (spMap (algebraMap V K))
  have hk := IsPullback.of_hasPullback A.hom (spMap (IsLocalRing.residue V))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hk
  have hσ : ∃ (σ : LB.Sec ((pw L.L d).pull (pullback.fst A.hom (spMap (algebraMap V K))))) (k : _), σ.f k ≠ 0 := by
    rw [AmpleCrit.pull_pw_eq]
    obtain ⟨x⟩ : Nonempty ↥(pullback A.hom (spMap (algebraMap V K))) := inferInstance
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hs]; trivial)
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    refine ⟨s i, k, fun e => ?_⟩
    rw [e, Scheme.basicOpen_zero] at hk
    exact hk
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, ⟨t, -, a, x, hx, hxa⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hk hϖ hH σ hσ
  have hflat : g.Flat := by
    letI := g.toAlgebra
    have : Module.IsTorsionFree V O := Module.isTorsionFree_iff_algebraMap_injective.2 hg
    exact (inferInstance : Module.Flat V O)
  have : Surjective (spMap g) := by
    letI := g.toAlgebra
    have : Module.Flat V O := hflat
    have : IsLocalHom (algebraMap V O) := ‹_›
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := V) (B := O)
    exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := V) (B := O)⟩
  let B : Over (Sp O) := (Over.pullback (spMap g)).obj A
  let π : B.left ⟶ A.left := pullback.fst A.hom (spMap g)
  have h : IsGrpPullback B A (spMap g) π := isGrpPullback_pullback A _
  have hB := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have := hB.comm
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  obtain ⟨hLB, hr, ⟨c', -⟩, -⟩ := Out.CubePf.cubePull _ _ A B (cubeMapOf h) L c
  have cube : Triv (Theta B ((pw L.L d).pull π)) := by
    rw [AmpleCrit.pull_pw_eq]
    exact triv_theta_pw hLB ⟨c'.t, c'.isGen⟩ d
  obtain ⟨⟨t', ht', -⟩, H⟩ := SecPullIso.section_pull _ _ π _ _ _ hH (pull_isLB hH π)
    (Out.CubePf.idIsoL_isGen (pull_isLB hH π)) t
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap g) x
    (IsLocalRing.closedPoint O) (hx.trans (IsLocalRing.comap_closedPoint g).symm)
  have hu := SquareGenerated.exists_secs_sq_generate O F B hB _ (pull_isLB hH π) cube t'
    ⟨z, by rw [H t' ht']; exact (congrArg (· ∈ Out.nonzeroLocus t) hz₁).mpr (TopologicalSpace.Opens.mem_iSup.2 ⟨a, hxa⟩),
      hz₂⟩
  rw [← AmpleCrit.pull_pw_eq, AmpleCrit.pw_pw_eq, show (d : ℤ) * 2 = ((d * 2 : ℕ) : ℤ) by push_cast; rfl] at hu
  obtain ⟨m, u, hu⟩ := hu
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨m', u', hu'⟩ := AmpleCrit.exists_cover_of_pull g hflat A.hom π B.hom h.1 (isLB_pw hL _) u hu
  exact ⟨d * 2, m', u', by omega, hu'⟩

theorem relAmple_of_generic (hl : Out.Laws) (hA : IsAbelianScheme A) (c : CubicalStr A L)
    (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ) (hL' : L'.IsLB) (hw : LBIso L' (L.L.pull φ))
    (ha : Out.RelAmple A' L') (hk : Out.KTriv A' L') : Out.RelAmple A L.L := by
  have hL := L.isLB
  have := hA.proper
  let F := AlgebraicClosure K
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K F).comp (algebraMap V K))
  let g : V →+* O := ((algebraMap K F).comp (algebraMap V K)).codRestrict O.toSubring hO
  have : IsLocalHom g := hloc
  have hg : Function.Injective g := fun a b e =>
    IsFractionRing.injective V K ((algebraMap K F).injective (congrArg Subtype.val e))
  have ha₀ : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap V K))))
      (L.L.pull (pullback.fst A.hom (spMap (algebraMap V K)))) := by
    have e : LBIso (L.L.pull (pullback.fst A.hom (spMap (algebraMap V K)))) (L'.pull h.1.isoPullback.inv) := by
      refine (CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).1 ?_
      rw [CechPic.cls_pull hL, CechPic.cls_pull hL', (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 hw,
        CechPic.cls_pull hL, ← CechPic.pull_comp, IsPullback.isoPullback_inv_fst]
    obtain ⟨w, hw'⟩ := e
    exact relAmple_pull (f := 𝟙 _) (A' := Over.mk (pullback.snd A.hom (spMap (algebraMap V K))))
      (IsPullback.of_horiz_isIso ⟨h.1.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩) hL' (pull_isLB hL _)
      ((isGen_iff w).1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) ha
  obtain ⟨d, m, u, hd, hu⟩ := exists_generating hA c O F g hg ha₀
  let k := IsLocalRing.ResidueField O
  have : IsAlgClosed k := (valuationRing_henselian_and_lift_of_isAlgClosed O F).2.1
  let β : V →+* k := (IsLocalRing.residue O).comp g
  have hs : Out.RelAmple (Over.mk (pullback.snd A.hom (spMap β))) (L.L.pull (pullback.fst A.hom (spMap β))) := by
    let B : Over (Sp k) := (Over.pullback (spMap β)).obj A
    let π : B.left ⟶ A.left := pullback.fst A.hom (spMap β)
    have hB : IsGrpPullback B A (spMap β) π := isGrpPullback_pullback A _
    have hBA := PolPull.isAbelianScheme_of_isGrpPullback hA hB
    have := hBA.comm
    obtain ⟨hLB, hr, ⟨c', -⟩, -⟩ := Out.CubePf.cubePull _ _ A B (cubeMapOf hB) L c
    have hσ := exists_ne_zero π (eSec B (IsLocalRing.closedPoint k)) (isLB_pw hL d) u hu
    rw [AmpleCrit.pull_pw_eq] at hσ
    obtain ⟨σ, hσ⟩ := hσ
    obtain ⟨n, hn, hp⟩ := Nat.exists_infinite_primes (2 * d + ringChar k + 1)
    have hnk : (n : k) ≠ 0 := fun e => by
      rcases hp.eq_one_or_self_of_dvd _ ((ringChar.spec k n).1 e) with e' | e'
      · exact CharP.ringChar_ne_one e'
      · omega
    have hnV : IsUnit (n : V) := IsUnit.of_map β _ (by rw [map_natCast]; exact hnk.isUnit)
    have hnS : IsUnit (n : Γ(Sp V, ⊤)) := by
      simpa using hnV.map (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
    refine AmpleCrit.relAmple_of_effective abMulN_holds k (Field.toIsField k) B hBA ((cubeMapOf hB).rigLB L hLB hr) c'
      d σ hd hσ k (𝟙 _) n hp hnk (fun e => by have := Nat.le_of_dvd (by omega) e; omega) fun x hx ht => ?_
    have e : pushHom hB _ x = 1 := eq_one_of_triv hl hA c O F (spMap g)
      ((Category.id_comp _).trans (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (IsLocalRing.residue O))))
      hnS (fun y hy => eq_one_of_inK h hL hL' hw hk (spMap (algebraMap K F))
        ((Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (algebraMap O F))).symm.trans
          (Spec.map_comp (CommRingCat.ofHom (algebraMap V K)) (CommRingCat.ofHom (algebraMap K F)))) y (inK_of_triv hy))
      (pushHom hB _ x) (by rw [← map_pow, hx, map_one]) (AmpleCrit.triv_translDiff_push hB hL x ht)
    have e' := e.trans (map_one (pushHom hB (Over.mk (𝟙 _)))).symm
    exact Over.OverMorphism.ext (hB.1.hom_ext (congrArg (fun q => q.left) e') (by rw [Over.w, Over.w]))
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample V _ A.hom L.L d m u hd hA.proper hL hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap V K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K), ha₀⟩
    · refine ⟨k, inferInstance, β, ?_, hs⟩
      rw [IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)]
      ext a
      rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff β, isUnit_iff_ne_zero,
        not_not])
  obtain ⟨e, he, hv⟩ := veryAmpleBy_pw_of_affine_loci V _ A.hom _ m u (isLB_pw hL _) hu aff
  rw [AmpleCrit.pw_pw_eq, ← Nat.cast_mul] at hv
  exact (Unif.relAmple_iff_veryAmpleBy V A L.L hL).2 ⟨d * e, Nat.mul_pos (by omega) he, hv⟩

end DVR

theorem exists_sab_of_generic : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp V)) [GrpObj A] (tK : SAB H (Sp K)) (φ : tK.G.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback tK.G A (spMap (algebraMap V K)) φ → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → ∃ (t : SAB H (Sp V)) (ν : SABMap tK t (spMap (algebraMap V K))) (e : t.G ≅ A), ν.φ ≫ e.hom.left = φ ∧ IsMonHom e.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro hH hl _ E _ _ _ H V K _ _ _ _ _ _ A _ tK φ hA h ha hk
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨act, hact⟩ := CM.exists_oAct_extend_dedekind hH V K _ A tK.G φ hA h tK.act
  let i := h.1.isoPullback
  have hP := tK.PP.isLB
  obtain ⟨ρ, hρ⟩ := gen_chartPull (chartPullLinComb tK.PP.L i.inv (fun _ : PUnit => eSec tK.G ≫ i.hom)
    (fun _ : PUnit => eSec tK.G) (fun _ => 1) (𝟙 _) fun _ => by simp) tK.PP.rig tK.PP.rigGen
  obtain ⟨M, w, hw⟩ := hl.extend V K A (eSec tK.G ≫ i.hom)
    ((Category.assoc _ _ _).trans ((congrArg _ h.1.isoPullback_hom_fst).trans (cubeMapOf h).e_comm))
    (tK.PP.L.pull i.inv) (pull_isLB hP _) ρ hρ
  have hM : LBIso (M.L.pull φ) tK.PP.L := by
    have e := congrArg (CechPic.pull i.hom) ((CechPic.cls_eq_iff (pull_isLB M.isLB _) (pull_isLB hP _)).2 ⟨w, hw⟩)
    rw [CechPic.cls_pull M.isLB, CechPic.cls_pull hP, ← CechPic.pull_comp, ← CechPic.pull_comp, i.hom_inv_id,
      CechPic.pull_id] at e
    refine (CechPic.cls_eq_iff (pull_isLB M.isLB _) hP).1 ?_
    rw [CechPic.cls_pull M.isLB, ← e, IsPullback.isoPullback_hom_fst]
  have := ExtendRig.isOpenImmersion_etaK V K
  obtain ⟨PP, cub, h₁, h₂, h₃, m, hm⟩ := TripleExt.exists_sab_extension (Sp V) (Published.SemiAbelianHomExtension.isNormalScheme_dvr V) E H (Sp K)
    (spMap (algebraMap V K)) A (isSemiAbelian_of_isAbelianScheme A hA) act tK φ h hact M.L M.isLB hM
  have hw' : LBIso tK.PP.L (PP.L.pull φ) := by
    obtain ⟨w', hw', -⟩ := m.lin
    subst hm
    exact ⟨w', hw'⟩
  have hamp := relAmple_of_generic hl hA cub h hP hw' ha hk
  exact ⟨_, m, Iso.refl A, (Category.comp_id _).trans hm, inferInstanceAs (IsMonHom (𝟙 A)), hamp,
    kTriv_of_generic hl.globalFns hA cub hamp h hP hw' hk⟩

end GlobalTheory.GoodPol
