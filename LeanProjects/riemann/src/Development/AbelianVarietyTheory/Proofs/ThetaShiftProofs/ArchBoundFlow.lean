import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NfacParallelFlowV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorantStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nfac_of_add {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la l₁ l₂ : Wt X.Ψ r) (h : ∀ τ i, la τ i = l₁ τ i + l₂ τ i) :
    X.nfac la x = X.nfac l₁ x * X.nfac l₂ x := by
  simp only [Data.nfac, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_add (norm_pos_iff.mpr
    (div_ne_zero (FlowCoefficientBounds.dmin_ne X hx τ _) (FlowCoefficientBounds.dmin_ne X hx τ _))), h]
  congr 1
  push_cast
  ring

theorem arch_bound_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : (U.X k).dom) (C ep xi : ℝ) (κ : ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → 0 < C → 0 < ep → Even n → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xi) → ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 → ∃ hx : (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 ∈ (U.X k).dom, (∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep) ∧ (∀ (P : Frame (U.X k).Ψ r → ℂ) (ν : (U.X k).Ψ → ℝ), (U.X k).IsBddSec (laU U a' n k) P → ‖(U.X k).fj (laU U a' n k) ξ' ν P x.1‖ = Real.exp (4 * Real.pi * ∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ)) * ‖(U.X k).fj (laU U a' n k) ξ' ν P ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)‖) ∧ ∀ Hm, IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx⟩) Hm → ‖κ‖ / (lieFac Dw xi a' * (U.X k).nfac (laU U a' n k) ((U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1)) ≤ (C * (ep⁻¹) ^ (U.X k).Ψ.card) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re) ^ ((a' (τ, (i : ℕ)) : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U Uw k ξ' x C ep xi κ a' n hσ hU hξ hC hep hn hxi hκ
  have him : ∀ τ, (U.X k).tt ξ' x.1 τ +
      ((((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I)).im = ep := by
    intro τ; simp
  have hd := GlobalTheory.FjCauchy.flow_mem_dom (U.X k) hξ x.2
    (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) (fun τ => by rw [him]; exact hep)
  have ht : ∀ τ, (U.X k).tt ξ' ((U.X k).flow ξ'
      (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1) τ = ep := fun τ => by
    rw [GlobalTheory.FjCauchy.tt_flow (U.X k) hξ x.2 _ hd, him]
  refine ⟨hd, ht, ?_, ?_⟩
  · intro P ν hP
    rw [GlobalTheory.FjCauchy.fj_flow (U.X k) hP hξ ν x.2 _ hd, norm_mul, ← mul_assoc, Complex.norm_exp,
      ← Real.exp_add]
    have hs : ∑ τ, (ν τ : ℂ) * (((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) =
        ((∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Complex.ofReal_mul, mul_assoc]
    rw [hs]
    generalize (∑ τ, ν τ * (ep - (U.X k).tt ξ' x.1 τ) : ℝ) = S
    have : (4 * (Real.pi : ℂ) * Complex.I * ((S : ℂ) * Complex.I)).re = -(4 * Real.pi * S) := by
      simp
    rw [this, add_neg_cancel, Real.exp_zero, one_mul]
  · intro Hm hH
    have hb := (GlobalTheory.T.riemann_form_frame_periods_eq_majorant E H Dw l Xo c σ r U Uw k ⟨_, hd⟩ Hm hσ hU hH).2.2 xi a' hxi
    have hf := nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hn hξ x.1 x.2 _ hd
    have hadd := nfac_of_add (U.X k) hd (laU U a' n k) (laU U a' 0 k) (laU U 0 n k) (by
      intro τ j
      simp only [laU]
      split_ifs <;> simp <;> ring)
    have hN := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U 0 n k)
    have hA := FlowCoefficientBounds.nfac_pos (U.X k) hd (laU U a' 0 k)
    have hL := lieFac_pos Dw xi a'
    simp only [ht, Finset.prod_const, Finset.card_univ, Fintype.card_coe] at hf
    have hp : 0 ≤ ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹ :=
      Finset.prod_nonneg fun τ _ => (inv_pos.mpr (GlobalTheory.FjCauchy.tt_pos (U.X k) hξ x.2 τ)).le
    have he : 0 ≤ (ep⁻¹) ^ (U.X k).Ψ.card := by positivity
    rw [hκ, hadd, Real.mul_rpow hC.le hp, mul_assoc, mul_comm _ ((U.X k).nfac (laU U 0 n k) x.1), ← hf,
      Real.mul_rpow hC.le he]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hb (by positivity))
    dsimp only
    generalize (U.X k).flow ξ' (fun τ => ((ep - (U.X k).tt ξ' x.1 τ : ℝ) : ℂ) * Complex.I) x.1 = y at hN hA ⊢
    field_simp

end GlobalTheory.ArcQ
