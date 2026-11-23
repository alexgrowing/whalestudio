import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeierstrassCurve

theorem mem_coordOpen_two_iff_notMem_range_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (a : scheme W) : a ∈ coordOpen W 2 ↔ a ∉ Set.range (zero W) := by
  constructor
  · rintro h ⟨p, rfl⟩
    exact (zero_preimage_coordOpen_two W).le h
  · intro h
    by_contra ha
    have h₀ : a ∈ originOpen W :=
      ((originOpen_sup_coordOpen_two W).ge (Set.mem_univ a)).resolve_right ha
    let g := (scheme W).fromSpecResidueField a
    have hg : ∀ t, g t = a := fun t => Scheme.fromSpecResidueField_apply a t
    have e := (eq_comp_zero_iff W g).2 ⟨fun t _ => by
      change g t ∈ originOpen W
      rwa [hg], by
      refine (basicOpen_eq_bot_iff _).1 ?_
      rw [← Scheme.preimage_basicOpen, basicOpen_originParam]
      refine le_bot_iff.1 fun t ht => ha ?_
      have : g t ∈ coordOpen W 2 := ht.2
      rwa [hg] at this⟩
    refine h ⟨toSpec W a, ?_⟩
    have t : Spec ((scheme W).residueField a) := Classical.arbitrary _
    have := congrArg (fun f => f t) e
    simp only [Scheme.Hom.comp_apply, hg] at this
    exact this.symm

theorem exists_polAV_section_origin : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic], ∃ (A : PolAV (Spec (CommRingCat.of K))) (e : A.A ≅ GlobalTheory.WeierstrassCurve.schemeOver W) (θ : H0 A.L 1), (η[A.A]).left ≫ e.hom.left = GlobalTheory.WeierstrassCurve.zero W ∧ A.g = 1 ∧ ∀ a : A.A.left, a ∈ nonzeroLocus θ ↔ e.hom.left a ∉ Set.range (GlobalTheory.WeierstrassCurve.zero W) := by
  intro K _ W _
  obtain ⟨G, hc, he, -⟩ := exists_grpObj_weierstrass K W W.isUnit_Δ
  obtain ⟨h₁, h₂, h₃, h₄⟩ := originLB_polarisation K W hc he
  let A : PolAV (Spec (CommRingCat.of K)) :=
    { A := schemeOver W
      grp := G
      isAb := isAbelianScheme_schemeOver K W W.isUnit_Δ hc
      g := 1
      smoothDim := smoothOfRelativeDimension_toSpec W
      L := originLB W
      isLB := originLB_isLB W
      rigid := h₁
      sym := h₂
      ample := h₃
      ktriv := h₄ }
  refine ⟨A, Iso.refl _, LB.finPowSec (originLB_isLB W) (n := 0) (secToPow (originSec W) 1) (𝟙 _),
    (Category.comp_id _).trans he, rfl, fun a => ?_⟩
  have e := LB.nonzeroLocus_finPowSec (originLB_isLB W) (n := 0) (secToPow (originSec W) 1) (𝟙 _)
  rw [nonzeroLocus_secToPow _ le_rfl, nonzeroLocus_originSec] at e
  exact (Iff.of_eq (congrArg (fun U : (scheme W).Opens => (a : scheme W) ∈ U) e)).trans
    (mem_coordOpen_two_iff_notMem_range_zero W a)

end GlobalTheory.WeierstrassCurve
