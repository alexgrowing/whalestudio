import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE_RDWave
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDBdd

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem rd_iter_pow (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (M : ℕ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' →
      ∃ K : ℝ, ∀ s : ℂ, ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr M
  obtain ⟨Θ, hΘ, hid⟩ := hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  induction M with
  | zero =>
    intro F F' hF hF'
    obtain ⟨_, _, -, hFc, -⟩ := hF
    obtain ⟨_, _, -, hFc', -⟩ := hF'
    obtain ⟨K, hK⟩ := radial_boundedness P.k P.r Wp Wq D F F' hFc hFc'
    exact ⟨K, fun s => by simpa using hK s⟩
  | succ M ih =>
    intro F F' hF hF'
    obtain ⟨K1, hK1⟩ := ih (Θ 1 F) (Θ 0 F') (hΘ 1 F hF) (hΘ 0 F' hF')
    obtain ⟨K2, hK2⟩ := ih (Θ 3 F) (Θ 2 F') (hΘ 3 F hF) (hΘ 2 F' hF')
    refine ⟨K1 + K2, fun s => ?_⟩
    have e := hid s F F' hF hF'
    calc ‖s‖ ^ (M + 1) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        = ‖s‖ ^ M * ‖s * B.beta D (wvG D.z D.z' s F) F'‖ := by rw [norm_mul, pow_succ]; ring
      _ = ‖s‖ ^ M * ‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F') -
            B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖ := by rw [e]
      _ ≤ ‖s‖ ^ M * (‖B.beta D (wvG D.z D.z' s (Θ 1 F)) (Θ 0 F')‖ +
            ‖B.beta D (wvG D.z D.z' s (Θ 3 F)) (Θ 2 F')‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ K1 + K2 := by rw [mul_add]; exact add_le_add (hK1 s) (hK2 s)

theorem rd_pow_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (1 + x ^ N) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + x ^ N) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hx N])
  · calc (1 + x) ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * x ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + x ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem rd_decay (hI : RDIdent) : RDHyp fun k r Wp Wq _ _ _ _ _ _ D =>
    ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), NiceAll D F → NiceAll D F' → ∀ n : ℕ,
      ∃ C : ℝ, ∀ s : ℂ, ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3)) := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr F F' hF hF' n
  have hp := rd_iter_pow hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr
  obtain ⟨K0, hK0⟩ := hp 0 F F' hF hF'
  obtain ⟨KN, hKN⟩ := hp (n + 3) F F' hF hF'
  refine ⟨2 ^ (n + 3) * (K0 + KN), fun s => ?_⟩
  have hx : 0 ≤ ‖s‖ := norm_nonneg _
  have hb : 0 ≤ ‖B.beta D (wvG D.z D.z' s F) F'‖ := norm_nonneg _
  have hb0 : ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ K0 := by simpa using hK0 s
  have hbN := hKN s
  have hpos : 0 < 1 + ‖s‖ := by linarith
  have main : (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖ ≤ 2 ^ (n + 3) * (K0 + KN) := by
    calc (1 + ‖s‖) ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖
        ≤ 2 ^ (n + 3) * (1 + ‖s‖ ^ (n + 3)) * ‖B.beta D (wvG D.z D.z' s F) F'‖ :=
          mul_le_mul_of_nonneg_right (rd_pow_le _ hx _) hb
      _ = 2 ^ (n + 3) * (‖B.beta D (wvG D.z D.z' s F) F'‖ +
            ‖s‖ ^ (n + 3) * ‖B.beta D (wvG D.z D.z' s F) F'‖) := by ring
      _ ≤ 2 ^ (n + 3) * (K0 + KN) := mul_le_mul_of_nonneg_left (add_le_add hb0 hbN) (by positivity)
  have hr' : (1 + ‖s‖) ^ (-((n : ℝ) + 3)) = ((1 + ‖s‖) ^ (n + 3))⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    congr 1
    rw [show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hr', ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [main]

theorem radDecay_of_cut (hI : RDIdent) : RadDecay := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl ε G H hε hG hH Φ Ψ hΦ hΨ
    c hc n
  have hr : 0 < P.r := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  obtain ⟨C', hC'⟩ := rd_decay hI Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr G H
    ⟨ε, hε, hG⟩ ⟨ε, hε, hH⟩ n
  subst hz hz' hπ hπ'
  obtain ⟨C1, -, hC1⟩ := radial_beta_identity P.k P.r Wp Wq D μ hD.2.1
  refine ⟨‖C1‖ * C', fun s Wv hW => ?_⟩
  have hwv := radial_wave_identity P.k P.r Wp Wq D hr ε s G
  have hΦ' : ∀ y ∈ DomR P.k P.r D.z D.z', ((Wv Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D (wvG D.z D.z' s G)) y.1 y.2 := by
    intro y hy
    rw [hW Φ y.1 y.2, hΦ y hy, hwv.2 y hy, hl']
  rw [hl0, hC1 (wvG D.z D.z' s G) H (Wv Φ) Ψ (hwv.1 hG).2.1 hH.2.1 hΦ' hΨ c, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC' s) (norm_nonneg _)

end Formalism.FourierDecayAlt.P.CutSE
