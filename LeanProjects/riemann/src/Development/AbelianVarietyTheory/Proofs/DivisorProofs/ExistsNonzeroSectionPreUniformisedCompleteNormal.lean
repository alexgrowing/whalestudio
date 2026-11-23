import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ModelSection
open GlobalTheory.UU GlobalTheory.TwistLoc

theorem isUnit_gc {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (z : Z) {c : K} (hc : c ≠ 0) :
    IsUnit (gc q z c) := by
  have h1 : gc q z (1 : K) = 1 := by
    unfold gc gs
    exact (dif_pos trivial).trans ((congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  exact IsUnit.of_mul_eq_one (gc q z c⁻¹) (by rw [← gc_mul, mul_inv_cancel₀ hc, h1])

theorem exists_ne_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) :
    ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  have h1 := GlobalTheory.abelianSchemeLaws_all.1
  have h2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨v, hv⟩ := ThetaIntegral.exists_sec_ne_zero h1 h2 _ A (Kbar R) (jFK (R := R) (Kbar R))
  obtain ⟨n, c, a, ha⟩ := ExpTotal.exists_span h1.secBaseChange A 1 le_rfl (Kbar R) (jFK (R := R) (Kbar R))
    (SecM.toSec A.A v)
  choose d hd σ hσ using fun i => ExpTotal.exists_integral U 1 (a i)
  by_contra hn
  have hz : ∀ i j, (σ i).f j = 0 := fun i j => by
    by_contra h
    exact hn ⟨σ i, j, h⟩
  refine hv (Subtype.ext (funext fun j => ?_))
  refine sec_ext_val (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) (Kbar R)) A.A).left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) A.isLB (s := SecM.toSec A.A v) (s' := SecM.toSec A.A 0) (fun z JA hJA => ?_) j
  obtain ⟨JG, hJG⟩ := exists_good_pt U.P.L.isLB z
  let y := (snd (TFK (R := R) (Kbar R)) A.A).left ≫ U.gen.inv.left
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((y ≫ pullback.fst G.hom (jK R)) ≫ G.hom)
  let x : T ⟶ G := Over.homMk (y ≫ pullback.fst G.hom (jK R)) rfl
  have hy : y ≫ U.gen.hom.left = 𝟙 _ ≫ (snd (TFK (R := R) (Kbar R)) A.A).left := by
    rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
  refine (ha _ (𝟙 _) z JA hJA).trans (Eq.trans (Finset.sum_eq_zero fun i _ => ?_)
    (ThetaIntegral.sval_eq_zero _ (fun _ => rfl) _ _ _).symm)
  have e := hσ i _ y (lift (toUnit T) x).left (congrArg (fun q => q.left) (lift_snd (toUnit T) x)) z JA JG hJA hJG
  rw [ThetaIntegral.sval_eq_zero (σ i) (hz i)] at e
  have e₃ : y ≫ pullback.fst G.hom (jK R) ≫ G.hom = (y ≫ pullback.snd G.hom (jK R)) ≫ jK R :=
    (congrArg (y ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm
  have hu : IsUnit (gc (y ≫ pullback.fst G.hom (jK R) ≫ G.hom) z (d i)) := by
    have e₄ := (congrArg (gc · z (d i)) e₃).trans (ExpTotal.gc_map _ _ z _)
    exact e₄ ▸ isUnit_gc _ z ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hd i))
  have e₅ := hu.mul_right_eq_zero.1 e.symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero] at e₅
  have e₆ := (congrArg (fun q => sval (a i) q z JA) hy).symm.trans e₅
  exact (congrArg (_ * ·) e₆).trans (mul_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ U => exists_ne_zero U

end GlobalTheory.Mum.ModelSection
end
