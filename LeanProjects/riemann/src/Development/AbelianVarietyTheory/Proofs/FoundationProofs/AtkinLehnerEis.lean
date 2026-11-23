import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDirectionIndep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KillsTranslatesSumMulMeanDifferenceEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRegularizedEisensteinLatticeTerm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDilateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletFourierMixedTwistMultipleStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisAL

theorem dif_comm' (L L' : ℕ) (v w : ℤ × ℤ) (F : ℤ × ℤ → ℂ) :
    dif L v (dif L' w F) = dif L' w (dif L v F) := by
  funext x
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h : ∑ s ∈ Finset.range L, ∑ r ∈ Finset.range L', F (x + (s : ℤ) • v + (r : ℤ) • w)
      = ∑ r ∈ Finset.range L', ∑ s ∈ Finset.range L, F (x + (r : ℤ) • w + (s : ℤ) • v) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [add_right_comm]
  rw [h]
  ring

theorem lat_indep2 (j L L' : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ) (hj : 1 ≤ j) (hL : 0 < L) (hL' : 0 < L')
    (hΦ : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) (hv : Kills L v Φ) (hw : Kills L' w Φ) :
    lat j 0 L v Φ τ = lat j 0 L' w Φ τ := by
  set T : ℤ × ℤ → ℂ := fun y => trm j 0 ((y.1 : ℂ) * τ + y.2) with hT
  have hsv := GlobalTheory.LatSumZ.latsum_summable j L v τ hj hL
  have hsw := GlobalTheory.LatSumZ.latsum_summable j L' w τ hj hL'
  simp only [lat]
  calc ∑' x, Φ x * dif L v (dif L v T) x
      = ∑' x, Φ x * dif L' w (dif L' w (dif L v (dif L v T))) x :=
        (sum_dif_dif L' w Φ _ hL' hΦ hw hsv).symm
    _ = ∑' x, Φ x * dif L v (dif L v (dif L' w (dif L' w T))) x := by
        have c1 : ∀ F : ℤ × ℤ → ℂ, dif L' w (dif L v (dif L v F)) = dif L v (dif L v (dif L' w F)) := by
          intro F; rw [dif_comm' L' L w v (dif L v F), dif_comm' L' L w v F]
        rw [c1 T, c1 (dif L' w T)]
    _ = ∑' x, Φ x * dif L' w (dif L' w T) x := sum_dif_dif L v Φ _ hL hΦ hv hsw

theorem inv_eq_zero_of_parity (k L : ℕ) (χ : ℤ → ℂ) (f : ℍ → ℂ) (h : Inv k L χ f)
    (hp : χ (-1) * (-1) ^ k ≠ 1) : f = 0 := by
  funext τ
  have h1 := h (-1) (by simp) τ
  have e : ((-1 : SL(2, ℤ)) • τ) = τ := by
    rw [ModularGroup.SL_neg_smul, one_smul]
  rw [e] at h1
  simp at h1
  have : (1 - χ (-1) * (-1) ^ k) * f τ = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (by linear_combination -h2) hp
  · simpa using h2

theorem qs_eq_of_MF (k L : ℕ) (χ : ℤ → ℂ) (a a' : ℕ → ℂ) (hk : 1 ≤ k) (hL : 0 < L)
    (ha : MF k L χ a) (ha' : MF k L χ a') (h : ∀ n, n ≠ 0 → a n = a' n) : qs a = qs a' := by
  set K := a 0 - a' 0 with hK
  have hd : ∀ τ, qs a τ = qs a' τ + K := by
    intro τ
    have s := GlobalTheory.EisM.CharTwist.summable_of_polyB ha.1 τ
    have s' := GlobalTheory.EisM.CharTwist.summable_of_polyB ha'.1 τ
    unfold qs
    rw [s.tsum_eq_zero_add, s'.tsum_eq_zero_add]
    have : ∀ n : ℕ, a (n + 1) = a' (n + 1) := fun n => h _ (Nat.succ_ne_zero n)
    simp only [this, hK]
    simp
    ring
  suffices hK0 : K = 0 by funext τ; rw [hd, hK0, add_zero]
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  let τ0 : ℍ := ⟨2 * Complex.I, by simp⟩
  have i1 := ha.2 γ (by simp [γ]) τ0
  have i2 := ha'.2 γ (by simp [γ]) τ0
  have j1 := ha.2 1 (by simp) τ0
  have j2 := ha'.2 1 (by simp) τ0
  simp only [one_smul] at j1 j2
  rw [hd, hd] at i1
  simp [γ] at i1 i2 j1 j2
  set w : ℂ := ((L : ℂ) * τ0 + 1) ^ k with hw
  have hw1 : w ≠ 1 := by
    intro hw1
    have hn : ‖((L : ℂ) * τ0 + 1)‖ ≥ 2 := by
      have := Complex.abs_im_le_norm ((L : ℂ) * τ0 + 1)
      have him : ((L : ℂ) * τ0 + 1).im = 2 * L := by simp [τ0]; ring
      rw [him] at this
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
      rw [abs_of_nonneg (by positivity)] at this
      linarith
    have : ‖w‖ = 1 := by rw [hw1]; simp
    rw [hw, norm_pow] at this
    have h2 : (2 : ℝ) ^ k ≤ ‖((L : ℂ) * τ0 + 1)‖ ^ k := pow_le_pow_left₀ (by norm_num) hn k
    have h3 : (1 : ℝ) < 2 ^ k := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  rw [hd] at j1
  have hK1 : K = χ 1 * K := by linear_combination j1 - j2
  have hK2 : K = χ 1 * w * K := by linear_combination i1 - i2
  have h0 : (w - 1) * K = 0 := by linear_combination w * hK1 - hK2
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hw1)

end GlobalTheory.EisAL

namespace GlobalTheory.EisAL

theorem slz_diag (j N : ℕ) (g : ℍ → ℂ) (τ : ℍ) (hτ' : 0 < ((N : ℂ) * τ).im) :
    slz j !![(N : ℤ), 0; 0, 1] g τ = (N : ℂ) ^ (j - 1) * g ⟨(N : ℂ) * τ, hτ'⟩ := by
  unfold slz
  simp [Matrix.det_fin_two]
  left
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hτ']
end GlobalTheory.EisAL

namespace GlobalTheory.EisAL

theorem MF_smul (k L : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ) (r : ℂ) (h : MF k L χ a) : MF k L χ (r • a) := by
  obtain ⟨⟨C, A, hC⟩, hI⟩ := h
  have hq : qs (r • a) = fun τ => r * qs a τ := by
    funext τ; unfold qs; rw [← tsum_mul_left]; congr 1; funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨⟨‖r‖ * C, A, fun n => ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg r)
  · intro γ hγ τ
    rw [hq]; simp only
    rw [hI γ hγ τ]; ring

theorem qs_smul (a : ℕ → ℂ) (r : ℂ) (τ : ℍ) : qs (r • a) τ = r * qs a τ := by
  unfold qs; rw [← tsum_mul_left]; congr 1; funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem atkin_lehner_eis : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  intro j N l ω ν c₁ c₂ a b c d hdet hj hN hl hlN h1 h2
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : 0 < l := hl.pos
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  set E₁ := eis j c₁ (ch ω) (ch ν) with hE₁
  set E₂ := eis j c₂ (fun x => ch ω x * hat ν x) (fun _ => 1) with hE₂
  have hν1 : ch ν⁻¹ (-1) = ch ν (-1) := by
    unfold ch
    have e : ν ((-1 : ℤ) : ZMod N) * ν ((-1 : ℤ) : ZMod N) = 1 := by rw [← map_mul]; simp
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right e
  have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  by_cases hpar : ch ω (-1) * ch ν (-1) = (-1) ^ j
  swap
  · have z1 : qs E₁ = 0 := inv_eq_zero_of_parity j (N * l) _ _ h1.2 (by
      intro h; apply hpar; linear_combination (-1 : ℂ) ^ j * h - (ch ω (-1) * ch ν (-1)) * hs)
    have z2 : qs E₂ = 0 := inv_eq_zero_of_parity j (N * l) _ _ h2.2 (by
      intro h; apply hpar; rw [hν1] at h; linear_combination (-1 : ℂ) ^ j * h - (ch ω (-1) * ch ν (-1)) * hs)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [z1, z2]; funext τ; simp [slz]

  obtain ⟨φ, hφsum, hφtw⟩ := GlobalTheory.EisM.CharTwist.exists_coeffs ω
  have hhat : ∀ x : ℤ, hat φ x = ch ω x := fun x => by rw [hat_eq_sum_std]; exact hφsum _
  have hω0 : ch ω 0 = 0 := by simp only [ch, Int.cast_zero]; exact MulChar.map_zero ω

  obtain ⟨c', hMF', hlat'⟩ := GlobalTheory.EisForm.eis_latF_mf j l N (ch ν) (ch ω) (ch ν) φ hj hl0 hN
    (by rw [hhat, hω0]) (fun x => by simp [ch])
    (fun d hd => by
      have hd' : IsCoprime d (l : ℤ) := by push_cast at hd; exact hd.of_mul_right_left
      have hu : IsUnit (d : ZMod l) := isUnit_of_isCoprime d hd'
      refine ⟨fun y => ?_, fun x => by simp [ch, mul_comm]⟩
      rw [hφtw (d : ZMod l) y hu, mul_comm y]; rfl) hpar
  have hfun : hat φ = ch ω := funext hhat
  rw [hfun] at hMF' hlat'
  rw [mul_comm l N] at hMF'
  have hq1 : qs E₁ = qs (eis j c' (ch ω) (ch ν)) :=
    qs_eq_of_MF j (N * l) _ _ _ hj hNl h1 hMF' (fun n hn => by simp [hE₁, eis, hn])

  have hcop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hcu : IsUnit (c : ZMod N) := isUnit_of_isCoprime c ⟨-(l * b), a * d, by linear_combination hdet⟩
  have hau : IsUnit (a : ZMod l) := isUnit_of_isCoprime a ⟨N * d, -(b * c), by linear_combination hdet⟩
  set φ₂ : ZMod (N * l) → ℂ := fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z) with hφ₂
  obtain ⟨⟨C, hC0, hChat0⟩, hφ₂tw0⟩ := GlobalTheory.T.dirichletFourier_mixed_twist_multiple N l ν ω φ a c hN hl0 hcop hhat hφtw hcu hau
  have hChat : ∀ x : ℤ, hat φ₂ x = C * (ch ω x * hat ν x) := hChat0
  have hφ₂tw : ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y, φ₂ y = ch ω d * ch ν⁻¹ d * φ₂ (y * d) := hφ₂tw0
  have hhat0₂ : hat φ₂ 0 = 0 := by rw [hChat, hω0]; ring
  obtain ⟨c'', hMF'', hlat''⟩ := GlobalTheory.EisForm.eis_latF_mf j (N * l) 1 (fun _ => 1) (fun d => ch ω d * ch ν⁻¹ d)
    (fun _ => 1) φ₂ hj hNl one_pos hhat0₂ (fun _ => rfl)
    (fun d hd => ⟨fun y => hφ₂tw d (by rwa [mul_one] at hd) y, fun x => by simp⟩)
    (by rw [mul_one, hν1]; exact hpar)
  simp only [mul_one] at hMF''
  have hq2 : qs (C⁻¹ • eis j c'' (hat φ₂) fun _ => 1) = qs E₂ :=
    qs_eq_of_MF j (N * l) _ _ _ hj hNl (MF_smul _ _ _ _ _ hMF'') h2 (fun n hn => by
      simp only [hE₂, eis, Pi.smul_apply, smul_eq_mul, if_neg hn, hChat, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      field_simp)

  set Φ₁ := latF l (ch ν) φ with hΦ₁
  set Ψ := latF (N * l) (fun _ => 1) φ₂ with hΨ
  set K₁ : ℂ := 2 * (-2 * π * Complex.I / l) ^ j / (j - 1).factorial with hK₁
  set K₂ : ℂ := 2 * (-2 * π * Complex.I / ((N * l : ℕ) : ℂ)) ^ j / (j - 1).factorial with hK₂
  have hK₁0 : K₁ ≠ 0 := by
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    simp [hK₁, Real.pi_ne_zero, Complex.I_ne_zero, this, Nat.factorial_ne_zero]
  have hK₂0 : K₂ ≠ 0 := by
    have h1 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have h2 : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
    simp [hK₂, Real.pi_ne_zero, Complex.I_ne_zero, h1, h2, Nat.factorial_ne_zero]
  have hE₁lat : ∀ τ, qs E₁ τ = K₁⁻¹ * lat j 0 l (0, 1) Φ₁ τ := fun τ => by
    rw [hlat' τ, hq1, ← mul_assoc, inv_mul_cancel₀ hK₁0, one_mul]
  have hE₂lat : ∀ τ, lat j 0 (N * l) (0, 1) Ψ τ = K₂ * C * qs E₂ τ := fun τ => by
    have e := hlat'' τ
    have e2 : qs (eis j c'' (hat φ₂) fun _ => 1) τ = C * qs E₂ τ := by
      rw [← hq2, qs_smul, ← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
    rw [e, e2]; push_cast; ring
  let γ₀ : SL(2, ℤ) := ⟨!![a, b; l * c, N * d], by simp [Matrix.det_fin_two]; linear_combination hdet⟩
  have hδ : !![(N : ℤ) * a, b; N * l * c, N * d] = (γ₀ : M2) * !![(N : ℤ), 0; 0, 1] := by
    ext i k; fin_cases i <;> fin_cases k <;> simp [γ₀] <;> ring
  have hdet0 : 0 < (γ₀ : M2).det := by rw [γ₀.2]; exact one_pos
  have hdet1 : 0 < (!![(N : ℤ), 0; 0, 1] : M2).det := by simp [Matrix.det_fin_two]; exact_mod_cast hN
  obtain ⟨hcomp, hSL, -⟩ := GlobalTheory.EisM.slz_props j (qs E₁) hj
  refine ⟨(N : ℂ) ^ (j - 1) * K₁⁻¹ * (K₂ * C), by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ this) (inv_ne_zero hK₁0)) (mul_ne_zero hK₂0 hC0), ?_⟩
  rw [hδ, hcomp _ _ hdet0 hdet1]
  funext τ
  have hτ' : 0 < ((N : ℂ) * τ).im := by simp; exact mul_pos (by exact_mod_cast hN) τ.2
  set τ' : ℍ := ⟨(N : ℂ) * τ, hτ'⟩ with hτ'def
  have hout : slz j !![(N : ℤ), 0; 0, 1] (slz j (γ₀ : M2) (qs E₁)) τ = (N : ℂ) ^ (j - 1) * slz j (γ₀ : M2) (qs E₁) τ' := by
    exact slz_diag j N _ τ hτ'
  rw [hout, hSL γ₀ τ', hE₁lat]
  set Φ₁' : ℤ × ℤ → ℂ := fun y => Φ₁ (y.1 * (N * d) - y.2 * (l * c), -(y.1 * b) + y.2 * a) with hΦ₁'
  have htr : ∀ x : ℤ × ℤ, Φ₁' (x.1 * γ₀ 0 0 + x.2 * γ₀ 1 0, x.1 * γ₀ 0 1 + x.2 * γ₀ 1 1) = Φ₁ x := by
    intro x
    simp only [hΦ₁', γ₀]
    simp
    congr 1
    ext
    · simp only; linear_combination x.1 * hdet
    · simp only; linear_combination x.2 * hdet
  rw [GlobalTheory.EisM.lat_smul j l (0, 1) Φ₁ Φ₁' γ₀ τ' htr]
  have hv : ((0 : ℤ) * γ₀ 0 0 + 1 * γ₀ 1 0, (0 : ℤ) * γ₀ 0 1 + 1 * γ₀ 1 1) = ((l : ℤ) * c, (N : ℤ) * d) := by
    simp [γ₀]
  simp only [Prod.fst, Prod.snd] at hv ⊢
  rw [hv, GlobalTheory.T.regularizedEisensteinLatticeSum_dilate j l N _ Φ₁' τ τ' hN rfl]
  have hrow : (fun y : ℤ × ℤ => if (N : ℤ) ∣ y.1 then Φ₁' (y.1 / N, y.2) else 0) = Ψ := by
    funext y; exact GlobalTheory.T.latticeFunctionDivisibleFirst_substitution N l ν φ a b c d hdet hN hl0 y
  rw [hrow]
  have hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C := by
    refine ⟨∑ z, ‖φ₂ z‖, fun x => ?_⟩
    simp only [hΨ, latF]
    split_ifs
    · rw [one_mul]
      exact Finset.single_le_sum (f := fun z => ‖φ₂ z‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    · simpa using Finset.sum_nonneg fun z (_ : z ∈ Finset.univ) => norm_nonneg (φ₂ z)
  have hKl : Kills (N * l) (0, 1) Ψ := by
    simpa using GlobalTheory.EisForm.latF_kills (N * l) 1 hNl (fun _ => 1) φ₂ (fun _ => rfl) hhat0₂ 0 1 (by simp)
  have hKv : Kills l ((N : ℤ) * ((l : ℤ) * c), (N : ℤ) * d) Ψ := by
    have hsum0 : ∑ y, φ y = 0 := by rw [← GlobalTheory.EisForm.hat_zero, hhat, hω0]
    have hdl : (N : ZMod l) * (a : ZMod l) * (d : ZMod l) = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod l)) hdet
      push_cast at this; rw [ZMod.natCast_self] at this; linear_combination this
    intro x
    by_cases h : ((N * l : ℕ) : ℤ) ∣ x.1
    · calc ∑ r ∈ Finset.range l, Ψ (x - (r : ℤ) • ((N : ℤ) * ((l : ℤ) * c), (N : ℤ) * d))
          = ∑ r ∈ Finset.range l, ν (-(c : ZMod N) * (x.2 : ZMod N)) *
              φ ((a : ZMod l) * (x.2 : ZMod l) + (r : ZMod l) * (-1)) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            simp only [hΨ, latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
            rw [if_pos (by obtain ⟨m, hm⟩ := h; exact ⟨m - r * c, by push_cast at hm ⊢; rw [hm]; ring⟩)]
            simp only [hφ₂, one_mul, map_intCast]
            congr 2
            · push_cast; rw [ZMod.natCast_self]; ring
            · push_cast; linear_combination (-(r : ZMod l)) * hdl
        _ = 0 := by rw [← Finset.mul_sum, GlobalTheory.EisForm.sum_shift l φ _ _ isUnit_one.neg, hsum0, mul_zero]
    · refine Finset.sum_eq_zero fun r _ => ?_
      simp only [hΨ, latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
      rw [if_neg]
      intro h2; apply h
      have h3 : ((N * l : ℕ) : ℤ) ∣ (r : ℤ) * ((N : ℤ) * ((l : ℤ) * c)) := ⟨r * c, by push_cast; ring⟩
      simpa using dvd_add h2 h3
  rw [lat_indep2 j l (N * l) _ (0, 1) Ψ τ hj hl0 hNl hΨb hKv hKl, hE₂lat]
  have hD : (((γ₀ 1 0 : ℤ) : ℂ) * τ' + ((γ₀ 1 1 : ℤ) : ℂ)) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ₀ τ'
    simpa [UpperHalfPlane.denom] using this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EisAL
