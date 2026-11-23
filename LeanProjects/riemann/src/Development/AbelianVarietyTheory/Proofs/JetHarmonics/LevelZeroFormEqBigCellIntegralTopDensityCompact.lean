import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeasurePreservingSnocMeasurableEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityBigCellEqProdLevelWeightsMulTopFormStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelModuleFormEqIntegralOfCompactCoeffStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

lemma levWeight_nonneg (P : M.Par) (j : ℕ) (t : ℂ) : 0 ≤ KB.levW P j t := by
  unfold KB.levW
  split_ifs
  · exact Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg _ _ _ _
  · positivity

lemma ofFn_snoc_unit {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l : Fin (j + 1) => ((1 : ℕ), Fin.snoc (α := fun _ => ℂ) c t l)) =
      (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) ++ [((1 : ℕ), t)] := by
  rw [List.ofFn_succ']
  simp

lemma isLocPt_ofFn_unit {j : ℕ} (c : Fin j → ℂ) (hc : ∀ i, c i ≠ 0) :
    D.IsLocPt (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) j := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    exact ⟨le_rfl, hc i⟩
  · simp [D.ptSize, List.map_ofFn, List.sum_ofFn]

theorem levelZero_eq_integral_topVector_of_cpt :
    P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → MemLp (tv p H w) 2 volume ∧ B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H = ((∫ c, ‖tv p H w c‖ ^ 2 : ℝ) : ℂ) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have hmeas := GlobalTheory.T.aestronglyMeasurable_topVector_smoothCoefficient Wp Wq P p Cb H w hD hw hH.1
  set R : (j : ℕ) → (Fin j → ℂ) → ℝ := fun j c =>
    (p.RR H j w (List.ofFn fun l : Fin j => ((1 : ℕ), c l)) (List.ofFn fun l : Fin j => ((1 : ℕ), c l))).re with hR
  have hae : (fun c : Fin (P.r + 1) → ℂ => (∏ i : Fin (P.r + 1), KB.levW P ((i : ℕ) + 1) (c i)) * R (P.r + 1) c)
      =ᵐ[volume] fun c => ‖tv p H w c‖ ^ 2 := by
    filter_upwards [GlobalTheory.ae_coords_ne_zero (P.r + 1)] with c hc
    rw [← GlobalTheory.TopVec.Ew_eq_norm_tv_sq Wp Wq P p H w c, (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).1]
    rfl
  obtain ⟨hint, heq⟩ := GlobalTheory.iterated_integral_eq_integral_pi (P.r + 1) (KB.levW P) R (levWeight_nonneg P)
    (fun c hc => (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.2)
    ((hmeas.norm.pow 2).aemeasurable.congr hae.symm)
    (fun j hj c hc => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (Nat.lt_succ_iff.1 hj)
        (isLocPt_ofFn_unit c hc)
      have h3 := h1.re
      have h4 := integral_re h1
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3 h4
      simp only [hR, ofFn_snoc_unit]
      exact ⟨h3, by rw [h4, ← h2]⟩)
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 (hint.congr hae), ?_⟩
  rw [← integral_congr_ae hae, ← heq]
  have him := GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero hP Wp Wq P p Cb H w hD hH hw
  have h0 : p.RR H 0 w [] [] = B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hH.1 (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [← h0]
  apply Complex.ext
  · simp [hR]
  · simpa using him

end GlobalTheory.TopVec
