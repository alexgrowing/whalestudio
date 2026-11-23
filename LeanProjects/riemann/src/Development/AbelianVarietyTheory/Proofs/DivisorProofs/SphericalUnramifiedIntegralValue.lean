import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaSumGLComplex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCommensuratedKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsParamVecOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

namespace GlobalTheory.ZetaGL

theorem zeta_sum_GL_trivial : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (n : ℕ) (s : ℂ), (n : ℝ) / 2 < s.re → ∀ (z : ℂˣ) (φ : GL (Fin n) (Fv F v) → ℂ), ‖(z : ℂ)‖ = 1 →
    (∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ (e : Fin n → ℤ) (T : GL (Fin n) (Fv F v)), T.1 = Matrix.diagonal (fun i => ϖ.1 ^ e i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n, φ (k₁ * T * k₂) = (z : ℂ) ^ (∑ i, e i) * (qV F v : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |e i| : ℤ) : ℂ))) →
    (∀ g, ∀ k ∈ KGL v n, φ (g * k) = φ g) ∧
    HasSum (fun a : GL (Fin n) (Fv F v) ⧸ KGL v n => φ a.out)
      ((∏ j ∈ Finset.range n, (1 - (z : ℂ) * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹ * (1 - (z : ℂ)⁻¹ * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹) *
        ∏ j ∈ Finset.Icc 1 n, (1 - (qV F v : ℂ) ^ (-(2 * s + (j : ℂ))))) := by
  intro F _ _ v n s hs z φ hz hφ
  have hqN : qV F v ≠ 0 := GlobalTheory.LFun.qV_ne_zero v
  have hqC : (qV F v : ℂ) ≠ 0 := by exact_mod_cast hqN
  have hq1 : (1 : ℝ) < (qV F v : ℝ) := by
    show (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ); exact_mod_cast GlobalTheory.LFun.one_lt_absNorm v
  have hφ' : ∀ ϖ, IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (t : GL (Fin n) (v.adicCompletion F)),
      t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL v n, ∀ k₂ ∈ KGL v n,
      φ (k₁ * t * k₂) = (z : ℂ) ^ (∑ i, d i) * (qV F v : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) :=
    fun ϖ hϖ => hφ (Units.mk0 ϖ (GlobalTheory.LFun.SatCompare.ne_zero_of_isUnifV hϖ)) hϖ
  refine ⟨fun g k hk => ?_, ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV v
    have h0 : ϖ ≠ 0 := GlobalTheory.LFun.SatCompare.ne_zero_of_isUnifV hϖ
    obtain ⟨d, hd⟩ := (GlobalTheory.ZetaGL.cartan_existsUnique F v n hϖ (fun d => GlobalTheory.WeylGL.tor h0 d) (fun d => rfl) g).exists
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hd
    rw [mul_assoc (k₁ * _), hφ' ϖ hϖ d.1 _ rfl k₁ hk₁ k₂ hk₂, hφ' ϖ hϖ d.1 _ rfl k₁ hk₁ _ (mul_mem hk₂ hk)]
  · have hB : ∀ β ∈ Finset.univ.val.map (GlobalTheory.Core.Rk.TrivCoef.trivParGL v n),
        ‖(β : ℂ)‖ ≤ (qV F v : ℝ) ^ ((n : ℝ) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV F v : ℝ) ^ ((n : ℝ) / 2) := by
      intro β hβ
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hβ
      have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      have hre : (((n : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) / 2).re = ((n : ℝ) - 1 - 2 * ((i : ℕ) : ℝ)) / 2 := by simp
      simp only [GlobalTheory.Core.Rk.TrivCoef.trivParGL, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [← Complex.cpow_neg, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hqN),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hqN), Complex.neg_re, hre]
      exact ⟨Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith),
        Real.rpow_le_rpow_of_exponent_le hq1.le (by linarith)⟩
    have h := GlobalTheory.ZetaGL.zeta_sum_GL_complex GlobalTheory.UnramDoublingProof.unramifiedDoublingGL F v n s hs z φ hz hφ' ℂ 1 1 _
      (GlobalTheory.Core.Rk.TrivCoef.isSatVecGL_one v n) LinearMap.id ⟨1, fun g => by simp⟩ (fun _ => hB)
    have hnp : GlobalTheory.LFun.npow v (-(s + 1 / 2)) = (qV F v : ℂ) ^ (-(s + 1 / 2)) := rfl
    have e1 : eulerFac ((Finset.univ.val.map (GlobalTheory.Core.Rk.TrivCoef.trivParGL v n)).map (z * ·))
        (GlobalTheory.LFun.npow v (-(s + 1 / 2))) =
        ∏ j ∈ Finset.range n, (1 - (z : ℂ) * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹ := by
      rw [eulerFac_eq_prod, Multiset.map_map, Multiset.map_map, ← Finset.prod_range_reflect,
        ← Fin.prod_univ_eq_prod_range (fun j => (1 - (z : ℂ) * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - ((n - 1 - j : ℕ) : ℂ))))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ) := by
        have := i.2
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]
        push_cast
        ring
      simp only [Function.comp, GlobalTheory.Core.Rk.TrivCoef.trivParGL, Units.val_mul, Units.val_mk0, hnp]
      rw [hc, mul_assoc, ← Complex.cpow_add _ _ hqC]
      congr 4
      ring
    have e2 : eulerFac ((Finset.univ.val.map (GlobalTheory.Core.Rk.TrivCoef.trivParGL v n)).map fun β => (z * β)⁻¹)
        (GlobalTheory.LFun.npow v (-(s + 1 / 2))) =
        ∏ j ∈ Finset.range n, (1 - (z : ℂ)⁻¹ * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - (j : ℂ))))⁻¹ := by
      rw [eulerFac_eq_prod, Multiset.map_map, Multiset.map_map,
        ← Fin.prod_univ_eq_prod_range (fun j => (1 - (z : ℂ)⁻¹ * (qV F v : ℂ) ^ (-(s + (n : ℂ) / 2 - ((j : ℕ) : ℂ))))⁻¹)]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Function.comp, GlobalTheory.Core.Rk.TrivCoef.trivParGL, Units.val_inv_eq_inv_val, Units.val_mul,
        Units.val_mk0, hnp]
      rw [mul_inv, ← Complex.cpow_neg, mul_assoc, ← Complex.cpow_add _ _ hqC]
      congr 4
      ring
    have e3 : ∏ i ∈ Finset.range n, (1 - (qV F v : ℂ) ^ (-(2 * s + n - i))) =
        ∏ j ∈ Finset.Icc 1 n, (1 - (qV F v : ℂ) ^ (-(2 * s + (j : ℂ)))) := by
      refine Finset.prod_bij' (fun i _ => n - i) (fun j _ => n - j) (fun i hi => ?_) (fun j hj => ?_)
        (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
      · have := Finset.mem_range.1 hi
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
      · have := Finset.mem_Icc.1 hj
        exact Finset.mem_range.2 (by omega)
      · have := Finset.mem_range.1 hi
        show n - (n - i) = i
        omega
      · have := Finset.mem_Icc.1 hj
        show n - (n - j) = j
        omega
      · rw [Nat.cast_sub (Finset.mem_range.1 hi).le]
        congr 2
        ring
    rw [e1, e2, e3, ← Finset.prod_mul_distrib] at h
    simpa using h

end GlobalTheory.ZetaGL
