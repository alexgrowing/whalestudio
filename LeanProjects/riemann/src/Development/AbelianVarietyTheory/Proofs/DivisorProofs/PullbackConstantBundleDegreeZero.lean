import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHodgeCh2Omega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIntegralEqDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField

namespace GlobalTheory.CxDegIntegers

theorem exists_factor_spec_field (K : Type) [Field K] [NumberField K] (T : Scheme.{0})
    [Algebra ℚ Γ(T, ⊤)] (g : T ⟶ Sp (𝓞 K)) :
    ∃ φ : T ⟶ Sp K, φ ≫ spMap (algebraMap (𝓞 K) K) = g := by
  let a : 𝓞 K →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of (𝓞 K))).inv ≫ g.appTop).hom
  have ha : ∀ y : nonZeroDivisors (𝓞 K), IsUnit (a y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hm := Ideal.absNorm_mem (Ideal.span {y})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    have hn : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hy0
    have hu : IsUnit (a (c * y)) := by
      rw [hc, map_natCast, ← map_natCast (algebraMap ℚ Γ(T, ⊤))]
      exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn)).map _
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  let ψ : K →+* Γ(T, ⊤) := IsLocalization.lift (M := nonZeroDivisors (𝓞 K)) (S := K) ha
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  have e : CommRingCat.ofHom (algebraMap (𝓞 K) K) ≫ CommRingCat.ofHom ψ =
      (Scheme.ΓSpecIso (.of (𝓞 K))).inv ≫ g.appTop := by
    apply CommRingCat.hom_ext
    exact IsLocalization.lift_comp ha
  rw [Category.assoc, spMap, ← Spec.map_comp, e, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem cxDeg_pullback_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (M : (Sp (𝓞 K)).Modules) (r : ℕ),
    GlobalTheory.VB.IsVB M r → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) [IsIntegral Y],
    IsArithVar p 1 → ∀ q : Y ⟶ Sp (𝓞 K), cxDeg p ((Scheme.Modules.pullback q).obj M) r = 0 := by
  intro K _ _ M r hM k _ Y p _ hX q
  have hC := GlobalTheory.T.rational_fibre_projective_curve k Y p hX
  haveI := hC.isIntegral
  have hE := hM.pullback q
  have hL := hM.isLB_det
  have hB := hE.isLB_det
  have hA := Semi.LB.isLB_pull hL q
  have hB' := Semi.LB.isLB_pull hB (ratFibre.fst p)
  obtain ⟨φ, hφ⟩ := exists_factor_spec_field K (ratFibre p) (ratFibre.fst p ≫ q)
  have h2 := Semi.LB.isLB_pull hL (spMap (algebraMap (𝓞 K) K))
  have z : CechPic.pull (spMap (algebraMap (𝓞 K) K)) (CechPic.cls _ hL) = 0 := by
    rw [← CechPic.cls_pull hL _ h2]
    exact (CechPic.cls_eq_zero_iff h2).2 (ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local _ h2)
  have c : CechPic.cls _ hB = CechPic.cls _ hA :=
    ((CechPic.cls_eq_iff hA hB).2 (hM.lbIso_det_pullback q)).symm
  rw [ChernDegree.cxDeg_eq_ratDeg hX hE, ratDeg_eq_degLB hB, ← VB.IsProjCurve.degPic_cls hC hB',
    CechPic.cls_pull hB _ hB', c, CechPic.cls_pull hL q hA, ← CechPic.pull_comp, ← hφ,
    CechPic.pull_comp, z, map_zero, map_zero]

end GlobalTheory.CxDegIntegers
