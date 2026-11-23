import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeffStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopFormStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelFormsReal

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · simp only [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨by simp, hc l⟩
  · simp [D.ptSize, List.map_ofFn, Function.comp_def]

theorem ofFn_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l))
      = (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
  rw [List.ofFn_succ']
  simp

theorem integral_im_eq_zero {f : ℂ → ℂ} (hf : ∀ t, t ≠ 0 → (f t).im = 0) :
    (∫ t : ℂ, f t).im = 0 := by
  have h : f =ᵐ[volume] fun t => (((f t).re : ℝ) : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with t ht
    exact Complex.ext (by simp) (by simp [hf t ht])
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

theorem levelZero_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have key : ∀ (n j : ℕ), j + n = P.r + 1 → ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
      (p.RR H j w (List.ofFn fun l => ((1 : ℕ), c l)) (List.ofFn fun l => ((1 : ℕ), c l))).im = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc
      obtain rfl : j = P.r + 1 := hj
      exact (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.1
    | succ n ih =>
      intro j hj c hc
      rw [(GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (by omega) (isLocPt_ofFn c hc)).2]
      refine integral_im_eq_zero fun t ht => ?_
      have h := ih (j + 1) (by omega) (Fin.snoc c t) (fun l => by
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using ht
        · simpa using hc i)
      rw [ofFn_snoc] at h
      simp [Complex.mul_im, h]
  simpa using key (P.r + 1) 0 (by omega) (fun l => l.elim0) (fun l => l.elim0)

end GlobalTheory.LevelFormsReal
