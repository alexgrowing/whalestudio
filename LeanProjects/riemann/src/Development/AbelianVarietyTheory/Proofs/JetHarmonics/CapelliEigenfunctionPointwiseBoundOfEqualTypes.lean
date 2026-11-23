import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProofStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositiveStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionBoundThreePlacesStatement

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes

theorem gridNum_update {C b c : ℝ} {P : M.Par} {l : ℕ} {lam : Fin (2 * P.r + P.k + 1) → ℝ}
    (h : GridNum C b c P l lam) (x : ℝ) (hx : |x| ≤ b) :
    GridNum C b c (shP P P.u (Function.update P.u' l x)) l lam := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8, ?_, h10, h11⟩
  · change |Function.update P.u' l x l| ≤ b
    rwa [Function.update_self]
  · intro s hs
    obtain ⟨ha, hb⟩ := h9 s hs
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · change lam s + 1 / 2 ≤ Function.update P.u' l x (s.val + 1)
      rw [Function.update_of_ne hne]; exact ha hne
    · change Function.update P.u' l x (s.val + 2) + 1 / 2 ≤ lam s
      rw [Function.update_of_ne hne]; exact hb hne

theorem decay_le (r k N : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hN : 0 ≤ N) :
    (r + 1) ^ 2 * (r * (2 * r + k + 1) + 1) ≤ (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) := by
  set n := 2 * r + k + 1 with hn
  have h1 : r + 1 ≤ n := by linarith
  have h2 : r * n + 1 ≤ n ^ 2 := by nlinarith
  have h3 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h5 : 0 ≤ N * n ^ 2 := by positivity
  have h6 : 0 ≤ r * n + 1 := by nlinarith
  exact mul_le_mul h4 (by linarith) h6 (by positivity)

theorem thmBp_eig_eq : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) ∧ ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP hNF C C₃ C₀ hC hC₃ hC₀
  obtain ⟨c₃, Cb, -, hS⟩ := GlobalTheory.T.wignerShiftedPlacesExist_proof
  obtain ⟨C₄, Cc, hT⟩ := GlobalTheory.T.capelli_eigenfunction_bound_three_places hX hP hNF Cb C₃ (7 + C) C₀ hC₃ (by linarith) hC₀
  refine ⟨C₄, max (max Cc c₃) 0, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hstd hcase hp₀ hp₀' heig hA hlam hreg
  obtain ⟨hn₀, he, l, hl1, hl2, hg⟩ := hcase
  obtain ⟨hG, -⟩ := hstd
  obtain ⟨hf1, hf2, hf3⟩ := heig
  have hml : l ∈ Finset.Icc 1 P.k := Finset.mem_Icc.2 ⟨hl1, hl2.le⟩
  have hml' : l + 1 ∈ Finset.Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have Gl := hG l hml
  have Gl' := hG (l + 1) hml'
  have hc1 : 1 ≤ c := Gl.1
  have hcb : c + 2 ≤ b := Gl.2.1
  have hul : |P.u' l| ≤ b := Gl.2.2.2.2.1
  have hul' : |P.u' (l + 1)| ≤ b := Gl'.2.2.2.2.1
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  rw [abs_le] at hul hul'
  have hnb : (n₀ : ℝ) ≤ b := by linarith [hul.2, hul'.1]
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, -, b2, b3, -, a8, b8,
      c1, c2, -, c4⟩ := hS P Wp Wq p l n₀ (l + 1) l b he hl1 hl2 hg (fun i hi => (hG i hi).2.2.2.2.1) hnb
    (by linarith) (by omega) (by omega) hl1 hl2.le
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hdec := decay_le P.r P.k ((3 * (P.r + 1) : ℕ) : ℝ) hr hk (Nat.cast_nonneg _)
  have hM0 : 0 ≤ max (max Cc c₃) 0 := le_max_right _ _
  have hM1 : Cc ≤ max (max Cc c₃) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have hM2 : c₃ ≤ max (max Cc c₃) 0 := (le_max_right _ _).trans (le_max_left _ _)
  set M := max (max Cc c₃) 0 with hM
  rw [mul_assoc] at hA
  have hA1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ := by
    have e : ((2 * P.r + P.k + 1 : ℕ) : ℝ) = 2 * (P.r : ℝ) + P.k + 1 := by push_cast; ring
    rw [e, mul_assoc]
    have t1 := mul_le_mul_of_nonneg_right hM2
      (show 0 ≤ ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * (2 * (P.r : ℝ) + P.k + 1) + 1) by positivity)
    have t2 := mul_le_mul_of_nonneg_left hdec hM0
    have t3 : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hA2 : Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) := by
    rw [mul_assoc]
    have t1 := mul_le_mul_of_nonneg_right hM1
      (show 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) by positivity)
    rw [Nat.cast_add ((2 * P.r + 2) * p₀)] at hA
    linarith
  have Gp := gridNum_update Gl' (P.u' (l + 1) + (n₀ : ℝ)) (abs_le.2 ⟨by linarith [hul'.1], by linarith [hul.2]⟩)
  have Gm := gridNum_update Gl (P.u' l - (n₀ : ℝ)) (abs_le.2 ⟨by linarith [hul'.1], by linarith [hul.2]⟩)
  obtain ⟨hpos, hΛ, Yp, hWp, hLp⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c _ Wp Wqp pp lam hC (by rw [a1]; exact Gp) (by
    rw [a1]
    change ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤
      |P.u (l + 1) - Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (l + 1)|
    rw [Function.update_self, he _ hml', ← hn₀]
    exact le_abs.2 (Or.inr (by linarith)))
  obtain ⟨-, -, Ym, hWm, hLm⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c _ Wp Wqm pm lam hC (by rw [b1]; exact Gm) (by
    rw [b1]
    change ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - Function.update P.u' l (P.u' l - (n₀ : ℝ)) l|
    rw [Function.update_self, he _ hml, ← hn₀]
    exact le_abs.2 (Or.inl (by linarith)))
  have hgap : ∀ s t, s ≠ t → 2 * c ≤ |lam s - lam t| := by
    intro s t hst
    rcases lt_or_gt_of_ne hst with h | h
    · exact le_abs.2 (Or.inl (by linarith [Gl.2.2.2.2.2.2.1 s t h]))
    · exact le_abs.2 (Or.inr (by linarith [Gl.2.2.2.2.2.2.1 t s h]))
  exact hT P Wp Wq Wqp Wqm _ _ _ _ p pp pm f Ap Am ApPt AmPt b (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) A₀ n₀ p₀
    (n₀ * (P.r + 1)) (Pst lam c) (Pst lam c) Yp Ym 3 (3 * (P.r + 1)) (by linarith) hΛ le_rfl hn₀.le hp₀' a2 a3 b2 b3
    le_rfl (by omega) hpos hpos a8 b8 hf1 hf2 c1 c2 hA2 (c4 A₀ f hA1 (hf2 1)) hreg hWp hLp hWm hLm hp₀ lam lam' c
    hf3 hgap hlam (fun _ => le_rfl) (fun _ => le_rfl)

end GlobalTheory.capelliEigenfunction_pointwiseBound_of_equalTypes
