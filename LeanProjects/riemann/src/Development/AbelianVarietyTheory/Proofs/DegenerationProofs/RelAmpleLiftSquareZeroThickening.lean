import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecOnPullSurjectiveOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowSectionStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleThickening

theorem surjective_spec_of_isNilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem exists_sec_lbPow_of_pw {X : Scheme.{0}} {H : LB X} {n : ℕ} (σ : LB.Sec (pw H n)) :
    ∃ s : (lbPow H n).Sec, nonzeroLocus s = nonzeroLocus σ :=
  ⟨powSecMk n σ.f fun i j => (σ.compat i j).trans (congrArg (· * _) (by
      change (H.g i j ^ (n : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val])),
    nonzeroLocus_powSecMk n _ _⟩

theorem relAmple_of_sq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  intro A A' _ _ g hg h2 X X' β hβ _ L L' hL hL' hw hA
  have hn : IsNilpotent (RingHom.ker g) := ⟨2, h2⟩
  obtain ⟨d, -, m, s', hs'⟩ := (Unif.relAmple_iff_veryAmpleBy A' X' L' hL').1 hA
  have hP' : IsProper X'.hom := isProper_of_veryAmpleBy hs'
  have hs : Surjective (Spec.map (CommRingCat.ofHom g)) := surjective_spec_of_isNilpotent_ker g hg hn
  have hc : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) := .spec_of_surjective _ hg
  have : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hβ.flip hs
  have : IsClosedImmersion β := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hβ.flip hc
  have hp : IsProper (β ≫ X.hom) := by rw [hβ.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective β X.hom
  have : IsSeparated X.hom := NilProper.isSeparated_of_comp_surjective β X.hom
  have : IsProper X.hom := {}
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have h : IsAmpleLB (L.pull β) :=
    (isAmpleLB_of_relAmple_of_isAffine X' hL' hA).of_lbIso (LB.isLB_pull hL β) hw.symm
  refine (relAmple_iff_isAmpleLB_of_isAffine X hL).2 ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := β.surjective x
  obtain ⟨n, hn₁, s, hz, ha⟩ := h.exists_affine z
  have hH := isLB_lbPow hL n
  obtain ⟨s₀, hs₀⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hH β) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL β n).symm s
  obtain ⟨D, hD, e⟩ := AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent A A' g hg hn _ _ X.hom X'.hom
    β hβ _ ha
  obtain ⟨t, ht⟩ := secOn_pull_surjective_of_surjective A A' g hg _ _ X.hom X'.hom β hβ _ hH D hD
    (GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D))
  obtain ⟨k, hk, σ, hσ⟩ := GlobalTheory.T.exists_pow_section' _ _ β
    (SquareZero.mul_eq_zero_of_app_eq_zero A A' g hg h2 _ _ X.hom X'.hom β hβ) _ hH s₀ D (e.trans hs₀.symm) t ht
  obtain ⟨u, hu⟩ := exists_sec_lbPow_of_pw σ
  have e' : nonzeroLocus (secOfPowPow u) = D := (nonzeroLocus_secOfPowPow u).trans (hu.trans hσ)
  exact ⟨n * k, Nat.mul_pos hn₁ hk, secOfPowPow u, e'.ge (e.ge hz), e' ▸ hD⟩

end GlobalTheory.AmpleThickening
