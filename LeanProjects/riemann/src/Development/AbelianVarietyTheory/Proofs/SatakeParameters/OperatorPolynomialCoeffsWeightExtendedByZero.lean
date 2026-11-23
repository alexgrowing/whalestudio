import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MvPolynomial

theorem sum_castLE_of_vanish {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ r : Fin b, a ≤ r.1 → F r = 0) : ∑ r, F r = ∑ r : Fin a, F (Fin.castLE h r) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro r hr
  apply hF
  by_contra hlt
  exact hr ⟨⟨r.1, by omega⟩, rfl⟩

theorem polDY_colSub (D : D7) {N N' : ℕ} (hN : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (β : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (hβ : ∀ τ r c, c < r → β τ r c = 0) :
    MvPolynomial.map (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →+* MvPolynomial (GL3Theta.FrV D N') ℂ) (polDY D s Q (N' := N')) =
      polDY D s (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) Q) (N' := N') := by
  have e : (MvPolynomial.mapAlgHom (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →ₐ[ℂ] MvPolynomial (GL3Theta.FrV D N') ℂ)).comp
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))) =
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))).comp (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, i, c⟩
    have hc : (c : ℕ) < N' := lt_of_lt_of_le c.2 hN
    have h1 : ∀ r : Fin N, (r : ℕ) < N' := fun r => lt_of_lt_of_le r.2 hN
    simp only [AlgHom.comp_apply, aeval_X, colSub, dif_pos hc, dif_pos (h1 _), map_sum, map_mul, MvPolynomial.mapAlgHom_apply,
      map_X, map_C, algHom_C, algebraMap_eq, Matrix.submatrix_apply]
    simp only [RingHom.coe_coe, aeval_C, aeval_X, map_sum, map_mul, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [sum_castLE_of_vanish hN]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.castLE, MvPolynomial.algebraMap_apply, algebraMap_eq]
      ring
    · intro r hr
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hβ τ r ⟨c, hc⟩ (Fin.lt_def.2 (lt_of_lt_of_le c.2 hr))]
      simp
  exact DFunLike.congr_fun e Q

theorem wt_polDY_framePol : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, MvPolynomial.coeff α (polDY D s Q (N' := N')) ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  intro D N N' hN s ν Q hQ
  have hc : ∀ α, MvPolynomial.coeff α (polDY D s Q (N' := N')) ∈ WtPol ℂ (extNu N' ν) := by
    intro α β hβ
    have hβ0 : ∀ τ r c, c < r → β τ r c = 0 := fun τ r c h => (hβ τ).1 r c h
    have hB : IsBor (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) :=
      fun τ => ⟨fun r c h => (hβ τ).1 _ _ h, fun r => (hβ τ).2 _⟩
    have e1 := congrArg (MvPolynomial.coeff α) (polDY_colSub D hN s Q β hβ0)
    have e2 : ∀ (c : ℂ) (P : MvPolynomial (GL3Theta.FrV D N) ℂ), polDY D s (c • P) (N' := N') = c • polDY D s P (N' := N') :=
      fun c P => by unfold polDY; exact map_smul _ c P
    rw [MvPolynomial.coeff_map, hQ _ hB, e2, MvPolynomial.coeff_smul] at e1
    have e3 : (∏ τ, ∏ r, β τ r r ^ extNu N' ν τ r) = ∏ τ, ∏ r, (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN) r r ^ ν τ r := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      symm
      refine Fintype.prod_of_injective (Fin.castLE hN) (Fin.castLE_injective hN) _ _ ?_ ?_
      · intro r hr
        have hr' : ¬ (r : ℕ) < N := fun h => hr ⟨⟨r, h⟩, rfl⟩
        simp only [extNu, dif_neg hr', pow_zero]
      · intro r
        simp only [extNu, Matrix.submatrix_apply, Fin.coe_castLE, dif_pos r.2]
    rw [e3]
    exact e1
  refine ⟨hc, fun Θ => ?_⟩
  unfold framePol
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hc α)

end GlobalTheory.TwV.DelA

end
