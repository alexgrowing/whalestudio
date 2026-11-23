import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfCubeDivGeneratedField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionNeZeroFibreOfGenericSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleGenericLocal

theorem exists_relAmple (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  obtain ⟨V, hV, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec A (IsLocalRing.closedPoint O : Sp O)) trivial
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine O A hA V hV fun s => ⟨eSec A s, ?_, ?_⟩
  · exact ((IsLocalRing.specializes_closedPoint (R := O) s).map (eSec A).continuous).mem_open V.isOpen hmem
  · rw [← Scheme.Hom.comp_apply, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]
    rfl

theorem exists_sec_fibre {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) (A' : Over (Sp K))
    (φ : A'.left ⟶ A.left) (hpb : IsPullback φ A'.hom A.hom (spMap (algebraMap O K))) (N : LB A.left)
    (hN : N.IsLB) (t : (N.pull φ).Sec) (ht : ∃ j, t.f j ≠ 0) (K' : Type) [Field K'] (y : Sp K' ⟶ Sp O) :
    ∃ (s : (N.pull (pullback.fst A.hom y)).Sec) (j : _), s.f j ≠ 0 := by
  haveI := hA.proper
  haveI := hA.smooth
  obtain ⟨F⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom (pull_isLB hN (𝟙 A.left))
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨v, hv0, hv⟩ := (GlobalTheory.GenericSection.exists_sec_iff F (algebraMap O K) hpb
    (Category.comp_id φ).symm).1 ⟨t, ht⟩
  let g' : O →+* K' := (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom g') = y := by simp [g']
  have H' : IsPullback (pullback.fst A.hom y) (pullback.snd A.hom y) A.hom
      (Spec.map (CommRingCat.ofHom g')) := by
    rw [hy]
    exact IsPullback.of_hasPullback A.hom y
  exact (GlobalTheory.GenericSection.exists_sec_iff F g' H' (Category.comp_id _).symm).2
    (GlobalTheory.GenericSection.exists_ker_ne_zero _ g' hinj _ v hv0 hv)

section Cube

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.EffectiveCube

theorem exists_sections_cube_cover {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀) (N : LB B.left)
    (s : N.Sec) (hN : N.IsLB) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  obtain ⟨j, hj⟩ := hs
  haveI := hB.comm
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hB hH hamp hN
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) B.hom).flip
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  let π : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  have hD : (((snd T B).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T B).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ B := Over.homMk (pointOfClosedPoint B.hom y hy) (pointOfClosedPoint_comp B.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply B.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp B.hom y hy)
  have good : ∀ a : T ⟶ B, (Out.ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 B).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 B) = Out.ptSecT B (a * x) ≫ snd T B := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 B) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : B ⟶ B).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : B ⟶ B => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end Cube

theorem relAmple_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  intro O K _ _ _ _ _ _ _ _ A _ A' _ φ hA hpb M M' hM hM' e hamp
  obtain ⟨L, hL, hLa⟩ := exists_relAmple O A hA
  haveI := hA.proper
  haveI := hA.smooth
  have hpb' : IsPullback φ A'.hom A.hom (spMap (algebraMap O K)) := hpb.1
  haveI hA'p : IsProper A'.hom := MorphismProperty.of_isPullback hpb' hA.proper
  have hampφ : Out.RelAmple A' (M.pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr hM' (pull_isLB hM φ) e).1 ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' hM').1 hamp))
  have hne : Nonempty A'.left := ⟨eSec A' (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K A' (L.pull φ) (M.pull φ) hA'p hne
    (pull_isLB hL φ) (pull_isLB hM φ) hampφ
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div (LB.isLB_linComb hM _ _) hL
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (LB.div (lbPow (M.pull f) a) (L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB hL f)
  obtain ⟨t, ht⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN φ) (hN' φ)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM φ a) ⟨s, hs⟩
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨t', j, ht'⟩ := exists_sec_fibre A hA A' φ hpb' _ hN t ht K' y
  have hB : IsAbelianScheme ((Over.pullback y).obj A) := Out.TLinPf.isAb_pullback y A hA
  have hpbB : IsPullback (pullback.fst A.hom y) ((Over.pullback y).obj A).hom A.hom y :=
    IsPullback.of_hasPullback A.hom y
  have hLB : Out.RelAmple ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange hpbB hL (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hLa
  obtain ⟨t'', ht''⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst A.hom y) a).symm ⟨t', j, ht'⟩
  obtain ⟨r, u, hu⟩ := exists_sections_cube_cover ((Over.pullback y).obj A) hB (pull_isLB hL _) hLB _ t''
    (hN' _) ht''
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine _ (pull_isLB hM _)
    (GlobalTheory.relAmple_of_cube_div_generated K' ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y))
      (M.pull (pullback.fst A.hom y)) a r u hB.proper (pull_isLB hL _) (pull_isLB hM _) ha hLB hu)

end GlobalTheory.AmpleGenericLocal
