import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

section Bundles

variable {W X Y : Scheme.{0}}

theorem lbIso_pullback {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (GlobalTheory.chartPullPull L j) (GlobalTheory.chartPullPull M j) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (GlobalTheory.chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pull_comp {Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X}
    {b' : W ⟶ Z} (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_of_lbIso {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y) {a' : W ⟶ X}
    (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (GlobalTheory.chartPullPull M j) (chartPullSame L _ _ _ j fun _ => ha) h

end Bundles

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_forall_mem {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨a, ?_, fun R' _ g hg z => hle ?_⟩
  · rintro rfl
    simp at ha
  · exact fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)

theorem exists_forall_notMem {C : Set (Sp R)} (hC : IsClosed C)
    (h : ∀ z : Sp K, spMap (algebraMap R K) z ∉ C) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∉ C := by
  have hg : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) := by
    rw [(IsGenericPointHom.fractionField R K).range_eq]; rfl
  obtain ⟨z, hz⟩ := hg
  exact exists_forall_mem (V := ⟨Cᶜ, hC.isOpen_compl⟩) (hz ▸ h z)

theorem exists_isPullback_stalk {Y Y₀ : Scheme.{0}} {p : Y ⟶ Sp R} {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) :
    ∃ p₁, IsPullback φ p₁ p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  refine ⟨p₀ ≫ e.hom, h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) ?_⟩
  simpa using he.symm

theorem exists_lift_open {S S' Y Y' : Scheme.{0}} (p : Y ⟶ S) (V : S.Opens) {π : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {t : S' ⟶ S} (w : π ≫ p = p' ≫ t) (ht : ∀ z, t z ∈ V) :
    ∃ l : Y' ⟶ pullback p V.ι, l ≫ pullback.fst p V.ι = π := by
  refine ⟨pullback.lift π (IsOpenImmersion.lift V.ι (p' ≫ t) ?_) ?_, pullback.lift_fst _ _ _⟩
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact ht _
  · exact w.trans (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_hom {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p] (q : X ⟶ Sp R)
    [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

theorem exists_lbIso {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap (algebraMap R K))) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

theorem exists_projective_model {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Sp K) [IsProper f₀] {L₀ : LB X₀}
    (hL : IsAmpleLB L₀) (hL' : L₀.IsLB) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Sp R) (φ : X₀ ⟶ X) (H : LB X) (N : ℕ), IsProper f ∧
      IsPullback φ f₀ f (spMap (algebraMap R K)) ∧ H.IsLB ∧ IsAmpleLB H ∧ 1 ≤ N ∧ LBIso (lbPow L₀ N) (H.pull φ) := by
  obtain ⟨N, hN, M, s, hs⟩ := hL.exists_veryAmpleBy f₀
  obtain ⟨hs, hc⟩ := (ProjSpace.veryAmpleBy_iff f₀ s).1 hs
  let c := ProjSpace.toProj f₀ s hs
  let u := ProjSpace.baseChange M (algebraMap R K)
  have hu := ProjSpace.isPullback_baseChange M (algebraMap R K)
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : Mono (spMap (algebraMap R K)) := mono_specMap_localization (nonZeroDivisors R) K
  have : Flat u := MorphismProperty.of_isPullback (P := @Flat) hu.flip inferInstance
  have : Mono u := MorphismProperty.of_isPullback (P := .monomorphisms _) hu.flip
    (inferInstanceAs (Mono (spMap (algebraMap R K))))
  have : QuasiCompact u := MorphismProperty.of_isPullback (P := @QuasiCompact) hu.flip inferInstance
  have hp := isPullback_toImage_of_isClosedImmersion (c ≫ u) c u rfl
  have := isProper_str R M
  refine ⟨(c ≫ u).image, (c ≫ u).imageι ≫ PSpace.str R M, (c ≫ u).toImage,
    (ProjSpace.O1 R M).pull (c ≫ u).imageι, N, inferInstance, ?_, pull_isLB (ProjSpace.O1_isLB R M) _,
    (isAmple_projective_O_one R M).pull_of_isClosedImmersion _, hN, ?_⟩
  · have := hp.flip.paste_vert hu
    rwa [ProjSpace.toProj_str] at this
  · have h1 {Y : Scheme.{0}} (F : Y ⟶ PSpace R M) := pull_isLB (ProjSpace.O1_isLB R M) F
    refine LBIso.trans (isLB_lbPow hL' _) (pull_isLB (ProjSpace.O1_isLB K M) c) (pull_isLB (h1 _) _)
      (ProjSpace.lbIso_pullback_O1_toProj f₀ s hs).symm ?_
    refine LBIso.trans (pull_isLB (ProjSpace.O1_isLB K M) c) (h1 (c ≫ u)) (pull_isLB (h1 _) _)
      (lbIso_pull_of_lbIso (ProjSpace.lbIso_pull_O1 M (algebraMap R K)).symm c rfl) ?_
    exact lbIso_pull_pull (ProjSpace.O1_isLB R M) _ (Scheme.Hom.toImage_imageι _).symm

theorem exists_isAmpleLB {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [QuasiSeparated f]
    {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K} (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L H : LB X} {L₀ : LB X₀}
    (hL : L.IsLB) (hH : H.IsLB) (hL₀ : L₀.IsLB) (hA : IsAmpleLB H) {N : ℕ} (hN : 1 ≤ N)
    (e : LBIso L₀ (L.pull φ)) (e' : LBIso (lbPow L₀ N) (H.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) →
        IsAmpleLB (L.pull π) := by
  obtain ⟨a, ha, Ha⟩ := exists_lbIso f h (isLB_lbPow hL N) hH
    (LBIso.trans (pull_isLB (isLB_lbPow hL N) _) (isLB_lbPow (pull_isLB hL _) N) (pull_isLB hH _)
      (lbIso_lbPow_pull hL φ N).symm
      (LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow hL₀ N) (pull_isLB hH _) (lbIso_lbPow e N).symm e'))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  refine (isAmpleLB_pow_iff (pull_isLB hL π) hN).1 ((hA.pull_of_isAffineHom π).of_lbIso
    (isLB_lbPow (pull_isLB hL _) N) ?_)
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB hH _)
    (lbIso_lbPow_pull hL π N) (Ha R' g hg X' π f' hp.w)

end GlobalTheory.GenSpread
