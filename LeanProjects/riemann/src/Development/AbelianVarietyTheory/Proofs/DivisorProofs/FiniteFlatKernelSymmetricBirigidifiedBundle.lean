import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelOfAmpleBundleFiniteFlatOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialEvaluationsOfMemKernelSymmetricPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteRetractOfFiniteFlatStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlatP

theorem flat_of_finite_rep : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [GrpObj B],
    IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∀ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left → IsFinite H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x) → Flat H.hom := by
  intro R _ _ B _ hB N hN hamp M hM H j hj hfin hrep
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  refine GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal R H hfin (fun m _ => ?_)
  set f := spMap (algebraMap R (Localization.AtPrime m)) with hf
  have hB' : IsAbelianScheme ((Over.pullback f).obj B) := GlobalTheory.isAbelianScheme_pullback_obj f B hB
  haveI := hB'.comm
  have hpb := IsPullback.of_hasPullback B.hom f
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B N hB hN hamp
    (Localization.AtPrime m) f _ _ _ hpb
  have hML : (M.pull (pullback.fst B.hom f)).IsLB := pull_isLB hM _
  have hrep' := GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f B M hM H j hrep
  have hth := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ ((Over.pullback f).obj B) hB' hP _ hML
  have hcl : IsClosedImmersion ((Over.pullback f).map j).left := by
    have e : ((Over.pullback f).map j).left =
        pullback.map H.hom f B.hom f j.left (𝟙 _) (𝟙 _) (by simp [Over.w j]) (by simp) := by
      first
      | rfl
      | (apply pullback.hom_ext <;> simp [Over.pullback_map_left])
      | (simp only [Over.pullback_map_left]; apply pullback.hom_ext <;> simp)
    rw [e]
    haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
      ⟨fun _ _ hf hg => by haveI := hf; haveI := hg; infer_instance⟩
    exact MorphismProperty.pullback_map (P := @IsClosedImmersion) hj (inferInstance : IsClosedImmersion (𝟙 _)) (Over.w j).symm (by simp)
  have hfin' : IsFinite ((Over.pullback f).obj H).hom := by
    first
    | exact MorphismProperty.pullback_snd (P := @IsFinite) _ _ hfin
    | (haveI := hfin; exact (inferInstance : IsFinite (pullback.snd H.hom f)))
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hG (Localization.AtPrime m) ((Over.pullback f).obj B) hB' hP _ hML hth _ _ hcl hrep' hfin'

theorem exists_closed_rep : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∃ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro R _ B _ hB N hN hamp M hM
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hP : IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B hN hamp
  obtain ⟨h0, -, h2⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B M hM
  obtain ⟨H, j, hj, hrep⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG R B hB hP M (AbLaw.pw M 0) hM h0
  refine ⟨H, j, hj, fun T x => ?_⟩
  rw [← GlobalTheory.UU.inK_iff_memKL, h2 _ rfl T x]
  exact hrep T x

private theorem isFinite_of_closedImmersion_factor_through_finite {S : Scheme.{0}} {H F G : Over S} (j : H ⟶ G) (i : F ⟶ G)
    (m : H ⟶ F) (hm : m ≫ i = j) (hj : IsClosedImmersion j.left) (hF : IsFinite F.hom) : IsFinite H.hom := by
  haveI : IsSeparated (i.left ≫ G.hom) := by rw [Over.w i]; infer_instance
  haveI : IsSeparated i.left := IsSeparated.of_comp i.left G.hom
  haveI : IsClosedImmersion (m.left ≫ i.left) := by rw [← Over.comp_left, hm]; exact hj
  haveI : IsClosedImmersion m.left := IsClosedImmersion.of_comp m.left i.left
  rw [← Over.w m]; infer_instance

end GlobalTheory.KerFlatP

namespace GlobalTheory

open GlobalTheory.KerFlatP in

theorem kernel_finiteFlat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G2 G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P.pull (lift (𝟙 G) (𝟙 G)).left) → ∃ (H : Over (Sp R)) (i : H ⟶ G), IsClosedImmersion i.left ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
  intro R _ _ G _ hG P hP h1 h2 hsym hamp
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  obtain ⟨HL, _, iL, -, -, hfinL, -, hrepL⟩ := GlobalTheory.kernel_finiteFlat_subgroup R G hG _ hL hamp
  have hGG : IsAbelianScheme (G ⊗ G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper (G ⊗ G).hom := by
    show IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hL1 := pull_isLB hL (fst G G).left
  have hL2 := pull_isLB hL (snd G G).left
  have hN := GlobalTheory.CechPic.isLB_tens hL1 hL2
  have hNamp : Out.RelAmple (G ⊗ G) (GlobalTheory.CechPic.tens _ _) :=
    GlobalTheory.MumProd.SumPol.relAmple_prod G G hL hL hN
      (by rw [GlobalTheory.CechPic.cls_tens hL1 hL2 hN, GlobalTheory.CechPic.cls_pull hL _ hL1, GlobalTheory.CechPic.cls_pull hL _ hL2])
      hamp hamp

  obtain ⟨K, k, hk, hrepK⟩ := exists_closed_rep R (G ⊗ G) hGG _ hN hNamp P hP

  have hmemK : GlobalTheory.MemKL (G ⊗ G) P (lift (k ≫ fst G G) (k ≫ snd G G)) := by
    rw [lift_comp_fst_snd]; exact (hrepK K k).2 ⟨𝟙 K, Category.id_comp _⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym K _ _ hmemK
  obtain ⟨za, hza⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ ha)
  obtain ⟨zb, hzb⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ hb)
  have hfinHL2 : IsFinite (HL ⊗ HL).hom := by
    haveI := hfinL
    show IsFinite (pullback.fst HL.hom HL.hom ≫ HL.hom)
    infer_instance
  have hfinK : IsFinite K.hom := by
    refine isFinite_of_closedImmersion_factor_through_finite k (lift (fst HL HL ≫ iL) (snd HL HL ≫ iL)) (lift za zb) ?_ hk hfinHL2
    apply CartesianMonoidalCategory.hom_ext <;> simp [hza, hzb]
  have hflatK : Flat K.hom := flat_of_finite_rep R (G ⊗ G) hGG _ hN hNamp P hP K k hk hfinK hrepK

  set e : G ⟶ G ⊗ G := lift (𝟙 G) (1 : G ⟶ G) with he
  have hxe : ∀ {T : Over (Sp R)} (x : T ⟶ G), x ≫ e = lift x (1 : T ⟶ G) := by
    intro T x
    apply CartesianMonoidalCategory.hom_ext <;> simp [e]
  let H : Over (Sp R) := Over.mk (pullback.snd k.left e.left ≫ G.hom)
  let i : H ⟶ G := Over.homMk (pullback.snd k.left e.left) rfl
  haveI := hk
  have hi : IsClosedImmersion i.left := by
    show IsClosedImmersion (pullback.snd k.left e.left)
    infer_instance
  have hwK : pullback.fst k.left e.left ≫ K.hom = H.hom := by
    show _ = pullback.snd k.left e.left ≫ G.hom
    rw [← Over.w k, pullback.condition_assoc, Over.w e]
  let s : H ⟶ K := Over.homMk (pullback.fst k.left e.left) hwK
  have hs : s ≫ k = i ≫ e :=
    Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left]; exact pullback.condition)
  have hmemH : ∀ (T : Over (Sp R)) (x : T ⟶ G),
      (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
    intro T x
    constructor
    · intro htr
      obtain ⟨z, hz⟩ := (hrepK T _).1 (GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle R G hG P hP h1 h2 hsym T x htr)
      have hz' : z.left ≫ k.left = x.left ≫ e.left := by
        rw [← Over.comp_left, hz, ← hxe, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left x.left hz') ?_, ?_⟩
      · show pullback.lift z.left x.left hz' ≫ pullback.snd k.left e.left ≫ G.hom = T.hom
        rw [pullback.lift_snd_assoc, Over.w x]
      · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact pullback.lift_snd _ _ _)
    · rintro ⟨y, rfl⟩
      have hm : GlobalTheory.MemKL (G ⊗ G) P (lift (y ≫ i) (1 : T ⟶ G)) := by
        refine (hrepK T _).2 ⟨y ≫ s, ?_⟩
        rw [Category.assoc, hs, ← Category.assoc, hxe]
      exact (GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym T _ _ hm).1

  have hLi : GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) i :=
    GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym H i ((hmemH H i).2 ⟨𝟙 H, Category.id_comp _⟩)
  obtain ⟨zH, hzH⟩ := (hrepL H i).1 hLi
  have hfinH : IsFinite H.hom := isFinite_of_closedImmersion_factor_through_finite i iL zH hzH hi hfinL

  obtain ⟨r, hr⟩ := (hmemH K (k ≫ fst G G)).1 ha
  have hsr : s ≫ r = 𝟙 H := by
    haveI : Mono i.left := by
      show Mono (pullback.snd k.left e.left)
      infer_instance
    have h3 : s ≫ r ≫ i = 𝟙 H ≫ i := by
      rw [hr, ← Category.assoc, hs, Category.assoc]; simp [e]
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).1 (by simpa [Over.comp_left] using congrArg CommaMorphism.left h3)
  exact ⟨H, i, hi, hfinH, GlobalTheory.T.flat_of_finite_retract_of_finite_flat R H K s r hsr hfinH hfinK hflatK, hmemH⟩

end GlobalTheory
