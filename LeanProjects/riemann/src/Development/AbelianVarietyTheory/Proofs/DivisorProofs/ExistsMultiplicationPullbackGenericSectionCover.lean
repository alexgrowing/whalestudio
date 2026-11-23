import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulSecK
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.MulPull in
theorem mulPull_gen_labCover {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    (C : LabCover D) (m : ℕ) :
    ∃ u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]),
      u.IsGen := by
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hcube : HasGen C.P.L.L (thφ C.G (x3 C.G)) thε := ⟨C.P.c.t, C.P.c.isGen⟩
  have hrig : HasGen C.P.L.L (K := PUnit) (fun _ => eSec C.G) (fun _ => 1) := ⟨C.P.L.rig, C.P.L.rigGen⟩
  have hone : HasGen C.P.L.L (K := Fin 1) ![(1 : C.G ⟶ C.G).left] ![1] := by
    refine (hrig.pull (toUnit C.G).left).of_formEq hL (fun U _ h => ?_)
    simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, _root_.mul_one]
    rfl
  have hsym0 : HasGen C.P.L.L (K := Fin 2) ![(ι[C.G]).left, 𝟙 C.G.left] ![1, -1] := ⟨C.P.sym, C.P.sym_gen⟩
  have e1 : ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left = (ι[C.G]).left := by
    show ((𝟙 C.G) ≫ ι[C.G]).left = _
    rw [Category.id_comp]
  have e2 : (𝟙 C.G : C.G ⟶ C.G).left = 𝟙 C.G.left := rfl
  have hsym : HasGen C.P.L.L (K := Fin 2) ![(𝟙 C.G : C.G ⟶ C.G).left, ((𝟙 C.G)⁻¹ : C.G ⟶ C.G).left] ![1, -1] := by
    refine hsym0.inv.of_formEq hL (fun U _ h => ?_)
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e1, e2]
    simp only [neg_neg, zpow_one, _root_.mul_one]
    exact mul_comm _ _
  have H := hasGen_pow hL hcube (𝟙 C.G) hone hsym m
  have e3 : ((𝟙 C.G) ^ m : C.G ⟶ C.G).left = (mulA C.G m).left := by
    rw [← GlobalTheory.ZH.TorsFrame.comp_mulA]
  refine H.of_formEq hL (fun U _ h => ?_)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, e2, e3]
  push_cast
  rfl

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_mulSecK (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hR : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) (m : ℕ) (_hm : Odd m) (θ₀ : SecK C.P.L.L C.α 1) :
    ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  obtain ⟨u, hu⟩ := mulPull_gen_labCover C m
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hc : (mulA C.A.A m).left ≫ C.α = C.α ≫ (mulA C.G m).left := GlobalTheory.ZH.TorsFrame.mulA_comm C.α_cart m
  let S₀ := pullMulSec θ₀ (mulA C.A.A m).left (LB.pullGen C.P.L.L _ _ u C.α) (DVR.pullGen_isGen C.P.L.L _ _ u hu C.α)
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (mulA C.A.A m).left ≫ C.α)
      (fun k : Fin 2 => C.α ≫ (![𝟙 C.G.left, (mulA C.G m).left] : Fin 2 → _) k))
      (Sum.elim (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) (![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)] : Fin 2 → ℤ))
      (fun _ : Fin 1 => C.α) (fun _ => ((m ^ 2 : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Category.comp_id, hc]
    simp only [Nat.cast_one, zpow_one, zpow_neg, _root_.mul_one]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨S, hS⟩ := exists_sec hL hf S₀
  refine ⟨S, u, hu, fun Z p z J hJ => ?_⟩
  rw [hS Z p z J hJ, sval_pullMulSec θ₀ _ _ _ p z hJ, val_pull hJ, mul_comm]

end GlobalTheory.Mum
