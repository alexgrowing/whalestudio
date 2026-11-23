import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open GlobalTheory.Poinc.Sep.Coef

noncomputable section

namespace GlobalTheory.USep.EvG

theorem frame_ev : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)),
      (t.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val t r z J ^ (N₁ ^ 2) * val κ (r ≫ b.left) z J = 1) →
    ∃ c ∈ k₀, (val t (spMap ev) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN b hb hbdef t ht
  obtain ⟨-, hM₀, hβ, hw, -⟩ := hFB
  have HD : DescV ib β ev k₀ w := ⟨hk₀, ptsVia_of hβ, hk, hM₀, hw, fun _ _ _ h _ => h⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.FamPull.exists_kap D N₁
  let y : Over.mk (spMap ev) ⟶ D.P.A := toUnit (Over.mk (spMap ev)) ≫ b
  have hy : y ^ N₁ = 1 := by rw [← MonObj.comp_pow, hb, MonObj.comp_one]
  have hyd : RatPV β k₀ y.left := by
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]
    exact hbdef
  obtain ⟨c, hc, ec⟩ := kap_memV HD κ hκ y hyd z J J₀ hJ hJ₀
  rw [hy] at ec
  have h1 : val t (spMap ev) z J ^ (N₁ ^ 2) * val (Z := Sp K) κ y.left z J = 1 := ht.2 κ hκ (Sp K) (spMap ev) z J hJ
  obtain ⟨c', hc', ec'⟩ := GlobalTheory.Poinc.Sep.Coef.zpow_mem ⟨c, hc, ec⟩ (-1)
  set a := om (Z := Sp K) w z J J₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left with ha
  set bb := om (Z := Sp K) w z J J₀ y.left with hbb
  set T := val t (spMap ev) z J with hT
  set Kv := val (Z := Sp K) κ y.left z J with hKv
  have alg : (T * a * bb⁻¹) ^ (N₁ ^ 2) = (bb ^ ((N₁ : ℤ) ^ 2) * a⁻¹ * a ^ (1 - (N₁ : ℤ) ^ 2) * Kv) ^ (-1 : ℤ) := by
    have hK : Kv = (T ^ (N₁ ^ 2))⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hK]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    rw [← natCast_zsmul, ← natCast_zsmul]
    push_cast
    module
  obtain ⟨c'', hc'', ec''⟩ := GlobalTheory.Poinc.Sep.Coef.root_mem hk₀ (z := z) (s := (T * a * bb⁻¹).val) (n := N₁ ^ 2) (Nat.one_le_pow _ _ (by omega))
    ⟨c', hc', by rw [← Units.val_pow_eq_pow_val, alg]; exact ec'⟩
  refine ⟨c'', hc'', ?_⟩
  have e : T = (a⁻¹ * bb) * (T * a * bb⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e, Units.val_mul, ← ec'']
  rfl

end GlobalTheory.USep.EvG
