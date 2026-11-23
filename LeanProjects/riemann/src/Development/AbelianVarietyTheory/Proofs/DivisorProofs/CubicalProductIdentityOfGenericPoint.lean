import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.Poinc.Sep.CubInt

theorem cubProd_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b cχ : 𝟙_ (Over (Sp V)) ⟶ D.P.A),
    b ^ N = 1 → ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit (TF (R := V) (FractionRing V)) ≫ cχ)
        (toUnit (TF (R := V) (FractionRing V)) ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) =
      val χt (toUnit (TF (R := V) (FractionRing V))).left z J ^ N) →
    ∀ (T : Over (Sp V)) (z : T.left) J, Good D.P.L z J →
      ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit T ≫ cχ) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χt T.hom z J ^ N := by
  intro V _ _ D N b cχ hbN χt ht hgen T z J hJ
  have G := (grep_cubProd cχ b N).mul ((SymFrame.grep_gen χt ht (𝟙 _)).pow N).inv
  obtain ⟨s, hs, vs⟩ := G.out D.P.isLB (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => Eq.trans (by
      have hK : ∏ k : Fin 4, h (𝟙 _ ≫ ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] k) ^ DegPre.gtε k =
          (h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
            (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ := by
        rw [Fin.prod_univ_four, ← SymFrame.eta_eq]
        simp [DegPre.gtε, zpow_neg, zpow_one]
      have hP : ∀ i, h (cχ * b ^ i * b).left * (h (cχ * b ^ i).left)⁻¹ * (h (cχ * b).left)⁻¹ *
          (h (b ^ i * b).left)⁻¹ * h cχ.left * h (b ^ i).left * h b.left *
          (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹ =
          (h (cχ * b ^ (i + 1)).left / h (b ^ (i + 1)).left) / (h (cχ * b ^ i).left / h (b ^ i).left) *
            ((h (cχ * b).left)⁻¹ * h cχ.left * h b.left *
              (h (1 : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ D.P.A).left)⁻¹) := by
        intro i
        rw [_root_.mul_assoc cχ, ← pow_succ]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_div]
        abel
      rw [Finset.prod_congr rfl (fun i _ => hP i), Finset.prod_mul_distrib,
        Finset.prod_range_div (fun i => h (cχ * b ^ i).left / h (b ^ i).left), Finset.prod_const, Finset.card_range, hK,
        hbN, pow_zero]
      simp) (Fintype.prod_empty _).symm)
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB rfl s (LB.oneGen D.P.L) hs (oneGen_gen _)
  have hρ1 : ρ = 1 := by
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' D.P.isLB z₀
    have a := vs _ (toUnit (TF (R := V) (FractionRing V))) z₀ J₀ hJ₀
    rw [hρ _ _ z₀ J₀ hJ₀, val_one, _root_.mul_one] at a
    simp only [Category.comp_id] at a
    have a1 : gm (toUnit (TF (R := V) (FractionRing V))).left z₀ ⊤ ρ = 1 := by
      rw [a]
      exact mul_inv_eq_one.mpr (hgen z₀ J₀ hJ₀)
    have c := gm_top_eq ρ z₀
    rw [a1, Units.val_one, cst_eq, ← map_one (cstH z₀)] at c
    have d := cstH_inj z₀ c
    rw [← map_one (algebraMap V (FractionRing V))] at d
    have e := IsFractionRing.injective V (FractionRing V) d
    apply Units.ext
    have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
    apply hinj
    rw [Units.val_one, map_one]
    exact e.symm
  have a := vs T (toUnit T) z J hJ
  rw [hρ _ _ z J hJ, val_one, _root_.mul_one, hρ1, map_one] at a
  simp only [Category.comp_id] at a
  exact mul_inv_eq_one.mp a.symm

end GlobalTheory.Poinc.Sep.CubInt
