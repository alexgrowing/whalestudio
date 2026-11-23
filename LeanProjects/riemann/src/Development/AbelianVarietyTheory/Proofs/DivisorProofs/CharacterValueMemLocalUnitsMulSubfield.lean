import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

open GlobalTheory.Poinc.Sep.Coef (om tele root_mem prod_mem)

theorem chi_mem : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN a b hb hbdef χ hχ
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  have h2 : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hP : Coef.Idx.PowPts ib (fun _ : PUnit => β) := by
    intro T' g hg
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb T'.hom g hg
    exact ⟨e.trans (MulEquiv.piUnique fun _ : PUnit => (Over.mk g ⟶ B₀)).symm, fun x u => by cases u; exact he x⟩
  have hone : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left := by
    intro _
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb (spMap ev) _ h2
    have e1 := he 1
    rw [map_one] at e1
    rw [← e1]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have H : Coef.Idx.Desc ib (fun _ : PUnit => β) ev k₀ w :=
    ⟨hk₀, hP, hk, hM₀, hw, fun _ _ _ h i => h i, hone⟩
  have pc : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c a).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ GlobalTheory.UChart.cpt D a) ≫ β)
    rw [Category.assoc, hc a, ← Category.assoc, h2]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have pb : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ b).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]; exact hbdef
  have pbi : ∀ i : ℕ, Coef.Idx.RatP (fun _ : PUnit => β) k₀ ((toUnit (Over.mk (spMap ev)) ≫ b) ^ i).left := by
    intro i
    induction i with
    | zero => rw [pow_zero]; exact hone
    | succ i ih => rw [pow_succ]; exact Coef.Idx.ratP_mul hP hk ih pb
  set x := toUnit (Over.mk (spMap ev)) ≫ D.c a with hx
  set y := toUnit (Over.mk (spMap ev)) ≫ b with hy
  have hyN : y ^ N₁ = 1 := by rw [hy, ← MonObj.comp_pow, hb, MonObj.comp_one]
  have hcub := hχ.2 (Over.mk (spMap ev)) z J hJ
  simp only [MonObj.comp_pow] at hcub
  choose c hc' ec using fun i : ℕ => Coef.Idx.cub_mem H x (y ^ i) y pc (pbi i) pb z J J₀ hJ hJ₀
  set h : (Over.mk (spMap ev) ⟶ D.P.A) → ((Sp K).presheaf.stalk z)ˣ := fun p => om (Z := Sp K) w z J J₀ p.left with hh
  set G := h (x * y) * (h x)⁻¹ * (h y)⁻¹ * h 1 with hG
  obtain ⟨c₁, hc₁, e₁⟩ := prod_mem (Finset.range N₁) (fun i => ⟨c i, hc' i, ec i⟩)
  have key : (∏ i ∈ Finset.range N₁, ((h (x * y ^ i * y) * (h (x * y ^ i))⁻¹ * (h (x * y))⁻¹ * (h (y ^ i * y))⁻¹ *
      h x * h (y ^ i) * h y * (h 1)⁻¹) * @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y))) =
      (G⁻¹ * val χ (spMap ev) z J) ^ N₁ := by
    rw [Finset.prod_mul_distrib, tele h x y N₁ hyN]
    have e3 : (∏ i ∈ Finset.range N₁, @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y)) =
        val χ (spMap ev) z J ^ N₁ := hcub
    have e4 : ∀ A B C E : ((Sp K).presheaf.stalk z)ˣ, A⁻¹ * B * C * E⁻¹ = (A * B⁻¹ * C⁻¹ * E)⁻¹ :=
      fun A B C E => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    rw [e3, e4, ← mul_pow]
  rw [key] at e₁
  obtain ⟨c₂, hc₂, e₂⟩ := root_mem hk₀ (z := z) (s := (G⁻¹ * val χ (spMap ev) z J).val) (n := N₁) (by omega) ⟨c₁, hc₁, by rw [← Units.val_pow_eq_pow_val]; exact e₁⟩
  refine ⟨c₂, hc₂, ?_⟩
  have hGe : G = gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
      (gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left) := by
    rw [hG, hh, hx, hy, ← MonObj.comp_mul]
    rfl
  rw [← hGe, ← e₂, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.USep.EvG
