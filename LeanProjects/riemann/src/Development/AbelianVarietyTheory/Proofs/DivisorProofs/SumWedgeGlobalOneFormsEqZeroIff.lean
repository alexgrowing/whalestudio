import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctionalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)
      simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
        Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _
      simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
        Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
