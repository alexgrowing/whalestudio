import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LimPosOfLimEvTOfCompactPositivity
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveIsometryOfRadial

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
open Filter Topology

namespace GlobalTheory.PointwiseBoundDecay

theorem levelZero_limit_of_xiExists (hΞ : B.XiExists) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

theorem top_threshold_le (r k N : ℕ) :
    ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have h1 : 1 ≤ n := by linarith
  have h3 : n ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h4 : (r : ℝ) * n + 1 ≤ ((r : ℝ) + 1) * n := by nlinarith
  have h5 : ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have h6 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
    have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    linarith
  have h7 : ((r : ℝ) + 1) * n ≤ ((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3) :=
    mul_le_mul h5 h6 (by linarith) (by positivity)
  calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)
      ≤ ((r : ℝ) + 1) ^ 2 * (((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_left (h4.trans h7) (by positivity)
    _ = _ := by ring

open GlobalTheory.PointwiseBound in

theorem ptBound_of_xiExists (hXi : B.XiExists) (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), 1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) → (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) → LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  have hRad := GlobalTheory.WeightedFormPos.radialModuleForm_of_xiExists hXi
  have hSS := GlobalTheory.ListDuality.listDuality_cpt hRad
  have hVI := waveIsometry_of_radial hRad
  have hFP := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hXi
  have hI4 := GlobalTheory.LiftBoundCpt.liftBound_of_xiExists hXi hA hSS hFP
  obtain ⟨C₂, hC₂, hLS⟩ := Formalism.FourierDecayAlt.P.lemma_s_of_parts Formalism.FourierDecayAlt.P.lemma_s_induction_base
    Formalism.FourierDecayAlt.P.lemma_s_induction_up
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hTN hZN hE hB
  refine Formalism.FourierDecayAlt.P.point_bound_of_corollary_s Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (Formalism.FourierDecayAlt.P.vector_truncation_at_place p χ F hχ.2.2)
    (Formalism.FourierDecayAlt.P.limit_zero_at_place p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hTN ε hε) (hZN ε hε)
  have hG := cptCoef_apx P p.T.base hχ hF hε n
  have hPos := GlobalTheory.WeightedFormPos.posAt_of_cptCoef_of_xiExists hXi hA Wp Wq P p nn _ Y N (fun y => (hnn y).le) hG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn _ Y Λ K N C₂ hKN hC₂.le hPos
    (hLS Wp Wq P p nn _ Y Λ K N hK hΛ hPos (extension_at_zero hXi hA p nn _ Y N Cb hCb hG)
      (GlobalTheory.planeWave_bound_of_xiExists hXi hA hVI hSS hFP Wp Wq P p nn _ Y Λ K N Cb hCb hG hnn hWG)
      (hI4 Wp Wq P p nn _ Y Λ K N hG hnn hLG) (hI5 ε hε n))

theorem main : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ C₂ Cc : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ), 1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → LimEvT p χ F Y N → LimBd p nn F Y N → TBB.PtBound p F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  intro hA Cb
  have hXi : B.XiExists := Formalism.FourierDecayAlt.P.exists_auxiliary_xi
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_of_xiExists hXi hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Ca, hCa⟩ := levelZero_limit_of_xiExists hXi Cb
  obtain ⟨Ce, hE⟩ := GlobalTheory.LevelZeroLimit.limE_of_limEvT_of_xiExists hXi hA Cb
  refine ⟨C₂, max (max 0 c₃) (max Ca Ce), hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth hWG hLG hI5 hLim hBd
  set C : ℝ := max (max 0 c₃) (max Ca Ce) with hC
  have hC0 : 0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC3 : c₃ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCa' : Ca ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCe' : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hmono : ∀ c : ℝ, c ≤ C → c * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := fun c hc =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)).trans hth
  have hth1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A := by
    refine le_trans ?_ hth
    rw [mul_assoc, mul_assoc]
    exact (mul_le_mul_of_nonneg_right hC3 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (top_threshold_le P.r P.k N) hC0)
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCa Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA (hmono _ hCa'))
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA (hmono _ hCe') hLim hBd)
    (lemB_one q F)

end GlobalTheory.PointwiseBoundDecay
