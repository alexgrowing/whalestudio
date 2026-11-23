import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CccoefMono
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CutoffCompactApproximantsConvergeDecayClassStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinearStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelZeroApprox

theorem ccle_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : B.Mat k r → E} {c c' : ℝ} (h : B.CCle A m F c) (h' : B.CCle A m F' c') :
    B.CCle A m (F - F') (c + c') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rw [e] at h1
  simpa using h1

theorem ckOn_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U : Set (B.Mat k r)}
    {F F' : B.Mat k r → E} (h : B.CkOn m U F) (h' : B.CkOn m U F') : B.CkOn m U (F - F') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rwa [e] at h1

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_bump_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : B.Mat k r → E} (h : B.CkOn ⊤ (B.GV k r) H) (n : ℕ) :
    B.CkOn ⊤ (B.GV k r) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) := by
    have e : (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) = fun g => 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
      funext g
      rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
      rfl
    rw [e]
    exact contDiff_const.sub (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hcs h
end

theorem threshold (k r N l : ℕ) (hl : l ≤ N) :
    B.AB k r + 1 + 2 * ((r : ℝ) + 1) * ((5 + l * (2 * r + k + 1) : ℕ) : ℝ) ≤
      20 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  push_cast
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast hl
  set ρ : ℝ := (r : ℝ) + 1 with hρ
  set ν : ℝ := 2 * (r : ℝ) + k + 1 with hν
  have hρ1 : 1 ≤ ρ := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hkr : (k : ℝ) + r ≤ ν := by linarith
  have h4 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have h2 : ν ≤ ν ^ 2 := le_self_pow₀ hν1 (by norm_num)
  have h3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hS : (l : ℝ) * ν + ν ≤ N * ν ^ 2 + ν ^ 3 :=
    add_le_add (mul_le_mul hlN h2 (by linarith) (by linarith)) h3
  have hlν : 0 ≤ (l : ℝ) * ν := by positivity
  have h5 : 20 * ρ * ((l : ℝ) * ν + ν) ≤ 20 * ρ ^ 4 * (N * ν ^ 2 + ν ^ 3) :=
    mul_le_mul (by linarith) hS (by linarith) (by positivity)
  refine le_trans ?_ h5
  have a1 : ((k : ℝ) + r) * ρ ≤ ν * ρ := mul_le_mul_of_nonneg_right hkr (by linarith)
  have a2 : ρ ≤ ν * ρ := le_mul_of_one_le_left (by linarith) hν1
  have a3 : 0 ≤ ρ * ((l : ℝ) * ν) := by positivity
  nlinarith

theorem beta_approx : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  refine ⟨20, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs s w χ f A N hχ hf hfA hA hw ε₁ ε₂ h₁ h₂
  have hth := (threshold k r N w.length hw).trans hA
  obtain ⟨K₁, hK₁, hH₁, hX₁⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₁ (B.AB k r) _ hχ h₁ hf hfA hth
  obtain ⟨K₂, hK₂, hH₂, hX₂⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₂ (B.AB k r) _ hχ h₂ hf hfA hth
  obtain ⟨C, hC, hbd⟩ := GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le k r Wp Wq Bs s w (B.AB k r) le_rfl
  have hsq := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear k r Wp Wq Bs s w (B.AB k r) le_rfl 1
  have hc₁ := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε₁
  have hx₁ := ckOn_bump_smul hc₁
  have lo : ∀ {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ},
      B.CCle (B.AB k r) (5 + w.length * (2 * r + k + 1)) F c → B.CCle (B.AB k r) 5 F c :=
    fun h => Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (Nat.le_add_right _ _) h
  generalize D.cutF Bs χ f ε₁ = H₁ at *
  generalize D.cutF Bs χ f ε₂ = H₂ at *
  set X₁ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₁ g with hX₁def
  set X₂ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₂ g with hX₂def
  set b : (B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp)) → ℂ := fun X Z =>
    B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) X w) Z with hb
  change ∀ n, B.CCle _ _ (X₁ n) K₁ ∧ B.CCle _ _ (X₁ n - H₁) _ at hX₁
  change ∀ n, B.CCle _ _ (X₂ n) K₂ ∧ B.CCle _ _ (X₂ n - H₂) _ at hX₂
  change ∀ n, B.CkOn _ _ (X₁ n) at hx₁
  change ∀ X Z c c', _ → _ → _ → ‖b X Z‖ ≤ _ at hbd
  change ∀ X X' Z Z', _ → _ → _ → _ → _ → _ → b (X + (1 : ℂ) • X') Z = b X Z + 1 * b X' Z ∧
    b X (Z + (1 : ℂ) • Z') = b X Z + (starRingEnd ℂ) 1 * b X Z' at hsq
  change Tendsto (fun n => b (X₁ n) (X₂ n)) atTop (𝓝 (b H₁ H₂)) ∧
    ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖b (X₁ n - X₁ m) (X₁ n - X₁ m)‖ ≤ K / ((n : ℝ) + 1)
  clear_value X₁ X₂ b
  constructor
  · have key : ∀ n : ℕ, ‖b (X₁ n) (X₂ n) - b H₁ H₂‖ ≤ 2 * C * K₁ * K₂ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hd := ckOn_sub (hx₁ n) hc₁
      have e1 := (hsq H₁ (X₁ n - H₁) (X₂ n) (X₂ n) hc₁ hd ⟨_, hH₁⟩ ⟨_, (hX₁ n).2⟩ ⟨_, lo (hX₂ n).1⟩
        ⟨_, lo (hX₂ n).1⟩).1
      have e2 := (hsq H₁ H₁ H₂ (X₂ n - H₂) hc₁ hc₁ ⟨_, hH₁⟩ ⟨_, hH₁⟩ ⟨_, lo hH₂⟩ ⟨_, lo (hX₂ n).2⟩).2
      simp only [one_smul, add_sub_cancel, one_mul, map_one] at e1 e2
      have b1 := hbd _ _ _ _ hd (hX₁ n).2 (lo (hX₂ n).1)
      have b2 := hbd _ _ _ _ hc₁ hH₁ (lo (hX₂ n).2)
      have e : b (X₁ n) (X₂ n) - b H₁ H₂ = b (X₁ n - H₁) (X₂ n) + b H₁ (X₂ n - H₂) := by
        rw [e1, e2]; ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) key ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C * K₁ * K₂)
  · refine ⟨4 * C * K₁ * K₁, fun n m hnm => ?_⟩
    have hd := ckOn_sub (hx₁ n) (hx₁ m)
    have c1 := ccle_sub (hX₁ n).2 (hX₁ m).2
    rw [sub_sub_sub_cancel_right] at c1
    have hle : K₁ / ((m : ℝ) + 1) ≤ K₁ / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact div_le_div_of_nonneg_left hK₁ (by positivity) (by linarith)
    have c2 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c c1 (add_le_add_right hle (K₁ / ((n : ℝ) + 1)))
    have c3 := ccle_sub (hX₁ n).1 (hX₁ m).1
    refine (hbd _ _ _ _ hd c2 (lo c3)).trans (le_of_eq ?_)
    ring

end GlobalTheory.LevelZeroApprox
