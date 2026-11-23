import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem weilIs_uTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u x hx a b c hc
  have hpos : (S.r * S.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have hζ : IsUnit S.ζ := S.prim.isUnit hpos
  obtain ⟨c₀, hc₀⟩ := (hζ.pow (S.r * S.N * (eStd S.g _ a b).val)).map (algebraMap o S.R)
  have H := ρ.weil a b c₀ hc₀
  have hf : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    exact (Spec.map_comp (CommRingCat.ofHom u.yK)
      (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))).symm
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk (spMap y₀) ((Category.comp_id _).trans hf.symm)
  have H' := CommPairing.weilIs_pull hL.globalFns ρ.P.isAb ρ.P.isLB h H
  have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn c₀) = unitOn c := by
    refine Units.ext ?_
    refine (congrArg (fun q => q.hom c₀.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y₀))).symm.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom (y₀ c₀.val) =
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c.val
    rw [hc, hc₀]
  rw [e] at H'
  exact (weilIs_grpPullback_of_comm' _ _ ρ.P.A u.A.A (spMap u.yK) u.φ ρ.P.L u.A.L ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (x a) (x b) (h ≫ ρ.pt a) (h ≫ ρ.pt b) (unitOn c) (hx a).symm (hx b).symm).2 H'

end GlobalTheory.ZH
end
