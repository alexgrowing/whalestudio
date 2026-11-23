import Mathlib
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassSchemeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve

theorem exists_mem_coordOpen_two {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : Sp R) :
    ∃ x : scheme W, toSpec W x = s ∧ x ∈ coordOpen W 2 := by
  have : Module.Finite (Polynomial R) W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  have : FaithfulSMul (Polynomial R) W.toAffine.CoordinateRing :=
    ⟨fun {p q} h => by
      have e := congrArg (fun a => (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).repr a 0)
        (h (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine 0))
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at e
      exact (mul_one p).symm.trans (e.trans (mul_one q))⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (Polynomial R) W.toAffine.CoordinateRing
    (PrimeSpectrum.comap (Polynomial.evalRingHom 0) s)
  refine ⟨chartZ W y, ?_, (opensRange_chartZ W).le ⟨y, rfl⟩⟩
  refine (Scheme.Hom.comp_apply (chartZ W) (toSpec W) y).symm.trans ?_
  rw [chartZ_toSpec]
  change PrimeSpectrum.comap (algebraMap R W.toAffine.CoordinateRing) y = s
  rw [IsScalarTower.algebraMap_eq R (Polynomial R), PrimeSpectrum.comap_comp_apply, hy]
  have e : (Polynomial.evalRingHom (0 : R)).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    ext; simp
  exact congrArg (fun f => PrimeSpectrum.comap f s) e

theorem exists_keyIn_iso_elliptic (R : Type) [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ (x : KeyIn R) (e : x.P.A ≅ schemeOver W), x.P.g = 1 ∧ eSec x.P.A ≫ e.hom.left = zero W ∧
      Out.nonzeroLocus x.th = e.hom.left ⁻¹ᵁ coordOpen W 2 := by
  obtain ⟨G, hc, h0, -⟩ := GlobalTheory.T.exists_commGrpObj_weierstrassScheme R W W.isUnit_Δ
  obtain ⟨hr, hs, ha, hk⟩ := originLB_polarisation R W hc h0
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      isAb := isAbelianScheme_schemeOver R W W.isUnit_Δ hc
      g := 1
      smoothDim := smoothOfRelativeDimension_toSpec W
      L := originLB W
      isLB := originLB_isLB W
      rigid := hr
      sym := hs
      ample := ha
      ktriv := hk }
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨v, -, hv⟩ := WeierstrassLie.isLieBasis_eps R W h0
  refine ⟨⟨P, le_rfl, rig, hrig, originSec W, fun s => ?_, ![v], hv⟩, Iso.refl _, rfl,
    (Category.comp_id _).trans h0, nonzeroLocus_originSec W⟩
  obtain ⟨x, hx, hx'⟩ := exists_mem_coordOpen_two W s
  exact ⟨x, hx, (nonzeroLocus_originSec W).ge hx'⟩

theorem exists_keyIn_elliptic (R : Type) [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ x : KeyIn R, x.P.g = 1 :=
  let ⟨x, _, h, _⟩ := exists_keyIn_iso_elliptic R W
  ⟨x, h⟩

end GlobalTheory.KeyPow
