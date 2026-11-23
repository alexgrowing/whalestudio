import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.StructureHomApply

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread.ClosedFac

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

def str {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) : CommRingCat.of R ⟶ Γ(H, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom q U)

theorem fromSpec_comp {H : Scheme.{0}} (q : H ⟶ Sp R) {U : H.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (str q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl

theorem str_res {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) (a : R) :
    str q U a = H.presheaf.map (homOfLE le_top).op (str q ⊤ a) :=
  (GlobalTheory.SectionsCommRing.map_structureHom q le_top a).symm

theorem appTop_str {H T : Scheme.{0}} (q : H ⟶ Sp R) {R' : Type} [CommRing R'] (g : R →+* R') (x : T ⟶ H)
    (t : T ⟶ Sp R') (w : x ≫ q = t ≫ spMap g) (a : R) : x.appTop (str q ⊤ a) = str t ⊤ (g a) := by
  have e {Y : Scheme.{0}} {S : Type} [CommRing S] (p : Y ⟶ Sp S) :
      str p ⊤ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop :=
    congrArg ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ·) (Scheme.Hom.appLE_eq_app (f := p) (U := ⊤))
  have : str q ⊤ ≫ x.appTop = CommRingCat.ofHom g ≫ str t ⊤ := by
    rw [e, e, Category.assoc, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => φ.hom a) this

theorem eq_zero_of_app_eq_zero {H : Scheme.{0}} {U : H.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (f : Γ(H, U) ⟶ B) (s : Γ(H, U)) (hs : (Spec.map f ≫ hU.fromSpec).app U s = 0) : f s = 0 := by
  have hz : ⊤ ≤ (Spec.map f ≫ hU.fromSpec) ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(H, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(H, U)).presheaf.map_id _
  have h2 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map f).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [h1, ← Scheme.ΓSpecIso_inv_naturality] at h2
  have h3 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz s = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hs, map_zero]
  rw [h2, CommRingCat.comp_apply] at h3
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective).1 h3

theorem exists_mul_eq_zero [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Z H : Scheme.{0}} (i : Z ⟶ H) (q : H ⟶ Sp R) [IsLocallyNoetherian H]
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) (U : H.affineOpens) :
    ∃ a : R, a ≠ 0 ∧ ∀ s ∈ i.ker.ideal U, str q U.1 a * s = 0 := by
  classical
  let M : Submonoid Γ(H, U.1) := (nonZeroDivisors R).map (str q U.1).hom
  let B := Localization M
  let φ : R →+* B := (algebraMap Γ(H, U.1) B).comp (str q U.1).hom
  have hφ (y : nonZeroDivisors R) : IsUnit (φ y) := IsLocalization.map_units B (⟨_, y, y.2, rfl⟩ : M)
  let ψ : K →+* B := IsLocalization.lift (M := nonZeroDivisors R) hφ
  obtain ⟨y, hy⟩ := h B (spMap (algebraMap Γ(H, U.1) B) ≫ U.2.fromSpec) (spMap ψ) (by
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact (IsLocalization.lift_comp (M := nonZeroDivisors R) hφ).symm)
  have key (s : Γ(H, U.1)) (hs : s ∈ i.ker.ideal U) : ∃ a : R, a ≠ 0 ∧ str q U.1 a * s = 0 := by
    have h1 := (y ≫ i).ideal_ker_le U (y.le_ker_comp i U hs)
    rw [hy] at h1
    have h2 : algebraMap Γ(H, U.1) B s = 0 :=
      eq_zero_of_app_eq_zero U.2 (CommRingCat.ofHom (algebraMap Γ(H, U.1) B)) s h1
    obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff M B s).1 h2
    exact ⟨a, nonZeroDivisors.ne_zero ha, hm⟩
  have := IsLocallyNoetherian.component_noetherian U
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (i.ker.ideal U)
  have hS' (s : S) : s.1 ∈ i.ker.ideal U := hS ▸ Ideal.subset_span s.2
  choose a ha ha' using fun s : S => key s (hS' s)
  refine ⟨∏ s, a s, Finset.prod_ne_zero_iff.2 fun s _ => ha s, fun s hs => ?_⟩
  rw [← hS] at hs
  refine Submodule.span_induction (fun s hs => ?_) (mul_zero _) (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hs
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨s, hs⟩ : S)), map_mul, mul_assoc, ha' ⟨s, hs⟩, mul_zero]
  · rw [mul_add, hu, hv, add_zero]
  · rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

theorem exists_lift (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R) (hi : IsClosedImmersion i)
    (hq : LocallyOfFiniteType q) (hq' : QuasiCompact q)
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  classical
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS, hSU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : H.Opens))).1
    isCompact_univ
  have : Fintype S := hS.fintype
  choose a ha ha' using exists_mul_eq_zero i q h
  refine ⟨∏ U : S, a U, Finset.prod_ne_zero_iff.2 fun U _ => ha U, fun R' _ g hg T x t w => ?_⟩
  set s := str q ⊤ (∏ U : S, a U) with hs
  have hx : IsUnit (x.appTop s) := by
    rw [hs, appTop_str q g x t w]
    exact hg.map _
  have hle : i.ker ≤ (H.basicOpen s).ι.ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) ?_ fun U u hu => ?_
    · rw [hSU, iSup_subtype]
    · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      have h0 : str q U.1.1 (∏ U : S, a U) * u = 0 := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ U), map_mul, mul_assoc, ha' _ u hu, mul_zero]
      have h1 : IsUnit ((H.basicOpen s).ι.app U.1.1 (str q U.1.1 (∏ U : S, a U))) := by
        rw [str_res, ← hs, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        refine IsUnit.map _ ?_
        refine (H.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => ?_
        refine (Scheme.mem_basicOpen _ _ z _).1 ?_
        rw [← Scheme.preimage_basicOpen]
        exact z.2
      exact h1.mul_right_eq_zero.1 (by rw [← map_mul, h0, map_zero])
  have hr : Set.range x ⊆ Set.range (H.basicOpen s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ x ⁻¹ᵁ H.basicOpen s
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hx]
    trivial
  refine ⟨IsOpenImmersion.lift _ x hr ≫ IsClosedImmersion.lift i _ hle, ?_⟩
  rw [Category.assoc, IsClosedImmersion.lift_fac, IsOpenImmersion.lift_fac]

end GlobalTheory.GenSpread.ClosedFac
