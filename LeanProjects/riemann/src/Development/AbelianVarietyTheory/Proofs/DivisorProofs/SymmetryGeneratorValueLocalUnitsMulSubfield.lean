import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportDownLineBundleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValuesMemSubfieldGaloisDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.SymVal

theorem sym_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ a
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  set φ' : Fin 2 → (D.P.A.left ⟶ D.P.A.left) := ![(ι[D.P.A]).left, 𝟙 D.P.A.left] with hφ'
  obtain ⟨t, ht, hmap⟩ := GlobalTheory.T.exists_generator_transport_down_lineBundleIso w hw hM₀ D.P.isLB φ' ![1, -1] D.sym D.sym_gen
  have hφ : ∀ k, φ' k ≫ β = β ≫ (![(ι[B₀]).left, 𝟙 B₀.left] : Fin 2 → (B₀.left ⟶ B₀.left)) k := by
    intro k
    fin_cases k
    · exact GlobalTheory.PolDeg.SymPol.inv_comm hpb
    · simp [hφ']
  have hpt : ∀ b : D.X, (spMap ev ≫ (D.c b).left) ≫ D.P.A.hom = spMap ev := fun b => by
    rw [Category.assoc, Over.w (D.c b)]; rfl
  have hdef : ∀ b : D.X, DefOver k₀ ((spMap ev ≫ (D.c b).left) ≫ β) := fun b => by
    have e : (spMap ev ≫ (D.c b).left) ≫ β = spMap (ev.comp ib) ≫ c₀ b := by
      rw [Category.assoc]
      erw [hc b]
      rw [← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp]
      rfl
    rw [e]
    exact GlobalTheory.Poinc.Sep.defOver_comp k₀ (GlobalTheory.Poinc.Sep.defOver_spMap k₀ _ hk) _

  have read : ∀ (x : Sp K ⟶ D.P.A.left) (z' : Sp K) (I : (Sp K ⟶ D.P.A.left) → D.P.L.ι)
      (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z' I → Good M₀ z' I₀ →
      val t x z' I₀ = gwx w z' I I₀ (x ≫ (ι[D.P.A]).left) * (gwx w z' I I₀ x)⁻¹ * val D.sym x z' I := by
    intro x z' I I₀ hI hI₀
    have H := hmap (Sp K) x z' (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => I (x ≫ φ' k))
      (fun k => hI₀ ((x ≫ φ' k) ≫ β)) (fun k => hI (x ≫ φ' k))
    rw [Category.comp_id, Fin.prod_univ_two] at H
    rw [val_of t x z' I₀ (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => by rw [Category.assoc]), H]
    simp only [hφ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg, Category.comp_id]
    rfl
  have hx₁ : (spMap ev ≫ (D.c 0).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c 0).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg, neg_zero]
  have hnorm : ∀ (z' : Sp K) (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z' I₀ →
      val t (spMap ev ≫ (D.c 0).left) z' I₀ = 1 := by
    intro z' I₀ hI₀
    choose I hI using fun χ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (χ z')
    have hIg : Good D.P.L z' I := hI
    rw [read _ z' I I₀ hIg hI₀, hx₁, _root_.mul_inv_cancel, _root_.one_mul, GlobalTheory.Poinc.ThetaOne.c_zero]
    have e1 : (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left = eSec D.P.A := rfl
    rw [e1, ← val_pull hIg, val_corr hIg D.sym_rig, val_one]
  obtain ⟨c, hc₀, hv⟩ := GlobalTheory.T.generator_values_mem_subfield_galoisDescent V₁ W₀ ib D.P.A D.P.isAb B₀ β hpb.1 M₀ hM₀ (Fin 2) (fun k => φ' k ≫ β) _ hφ
    ![1, -1] t ht K ev k₀ hk₀ hk _ (hpt 0) (hdef 0) hnorm _ (hpt a) (hdef a) z J₀ hJ₀
  refine ⟨c, hc₀, ?_⟩
  have r := read (spMap ev ≫ (D.c a).left) z J J₀ hJ hJ₀
  have hneg : (spMap ev ≫ (D.c a).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c (-a)).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg]
  rw [hneg] at r
  have key : val D.sym (spMap ev ≫ (D.c a).left) z J =
      (gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (D.c a).left) *
        val t (spMap ev ≫ (D.c a).left) z J₀ := by
    rw [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [key, Units.val_mul, hv]

end GlobalTheory.USep.EvG.SymVal
