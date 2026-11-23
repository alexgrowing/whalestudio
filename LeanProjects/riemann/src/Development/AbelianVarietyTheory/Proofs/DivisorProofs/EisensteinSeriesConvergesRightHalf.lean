import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightFirstColumnPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinLineRepsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinLineRepsSumStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisMidHt

theorem midSet_sum_rpow_lt_top : GlobalTheory.Published.EisensteinIsotropicLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ T, GlobalTheory.EisCT.IsTransv σ J (col0 X) T → ∀ s : ℝ, (n : ℝ) - 2 < s →
      ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h t.1.1 ^ s) < ⊤ := by
  intro hP F E _ _ _ _ _ σ n J r X Y L a h hS T hT s hs
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hS.2.2.2.1
  obtain ⟨hpos, hid⟩ := GlobalTheory.T.height_first_column_positive F E σ n J r X Y L a h hS
  obtain ⟨Yr, hY, f, hf, hfe⟩ := GlobalTheory.T.eisenstein_line_reps_exist F E σ n J r X Y L a h hS T hT
  obtain ⟨C, hC⟩ := GlobalTheory.T.eisenstein_height_lower_bound F E σ n J r X Y L a h hS s (by linarith)
  have hD := GlobalTheory.T.eisenstein_line_reps_sum hP F E σ n J r X Y L a h hS Yr hY (s - 1) (by linarith)
  have hnn : ∀ u, 0 ≤ GlobalTheory.EisMidHt.ht L a u := fun u =>
    mul_nonneg (finprod_nonneg fun _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
  let Q : Yr → E → ENNReal := fun y c => ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (y.1 + c • GlobalTheory.EisMidHt.firstColumn X)) ^ (-s))
  have hterm : ∀ t : GlobalTheory.EisCT.midSet σ J (col0 X) T,
      ENNReal.ofReal (h t.1.1 ^ s) = ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) * Q (f t).1 (f t).2 := by
    intro t
    obtain ⟨μ, hμ, he⟩ := hfe t
    have h1 := hid t.1.1
    rw [he, GlobalTheory.T.eisenstein_height_smul_invariant F E σ n J r X Y L a h hS μ hμ] at h1
    generalize hzdef : GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F ((f t).1.1 + (f t).2 • GlobalTheory.EisMidHt.firstColumn X)) = z at h1 ⊢
    have hz0 : 0 ≤ z := hzdef ▸ hnn _
    have hz : 0 < z := by
      rcases hz0.lt_or_eq with hz | hz
      · exact hz
      · rw [← hz, mul_zero] at h1; linarith
    have hht : h t.1.1 = GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) / z := by
      rw [eq_div_iff hz.ne']; exact h1
    rw [hht, Real.div_rpow hpos.le hz0, div_eq_mul_inv, ← Real.rpow_neg hz0,
      ENNReal.ofReal_mul (Real.rpow_nonneg hpos.le _)]
    subst hzdef; rfl
  calc ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, ENNReal.ofReal (h t.1.1 ^ s)
      = ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T,
          ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) * Q (f t).1 (f t).2 := tsum_congr hterm
    _ = ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) *
          ∑' t : GlobalTheory.EisCT.midSet σ J (col0 X) T, (fun p : Yr × E => Q p.1 p.2) (f t) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) * ∑' p : Yr × E, Q p.1 p.2 :=
          by gcongr; exact ENNReal.tsum_comp_le_tsum_of_injective hf _
    _ = ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) * ∑' y : Yr, ∑' c : E, Q y c := by rw [ENNReal.tsum_prod]
    _ ≤ ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) *
          ∑' y : Yr, ENNReal.ofReal C * ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (1 - s)) := by
          gcongr with y
          obtain ⟨h0, -, h1, h2⟩ := hY.1 y.1 y.2
          exact hC y.1 h0 h1 h2
    _ = ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X)) ^ s) *
          (ENNReal.ofReal C * ∑' y : Yr, ENNReal.ofReal (GlobalTheory.EisMidHt.ht L a (GlobalTheory.EisMidHt.adVec F y.1) ^ (1 - s))) := by
          rw [ENNReal.tsum_mul_left]
    _ < ⊤ := by
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
          have e : (1 - s) = -(s - 1) := by ring
          rw [e]; exact hD

end GlobalTheory.EisMidHt

end
