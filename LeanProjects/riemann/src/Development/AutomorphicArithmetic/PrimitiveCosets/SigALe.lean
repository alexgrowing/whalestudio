import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.PrimRead
import Development.AutomorphicArithmetic.PrimitiveCosets.CardPsiA

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem character_trivial_first_factor (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0) : Frame.TrivialOnFirstFactor (chr φ ψ) := by
  intro s hs
  apply Units.ext
  simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have e : ((chr φ ψ (φ.tau1 s)) : ℂ) = ψ (0, s) := by
    simp [chr, toE, Frame.tau1, Frame.iotaInv, Frame.iota]
    rfl
  rw [e, Units.val_one]
  exact h s hs

private theorem chr_bounded (Λ : Level) (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0)
    (hk : ψ ∉ keptA Λ H) : chr φ ψ ∈ H.Bounded Λ.KEPT := by
  have hT := character_trivial_first_factor φ ψ h
  have hsq : chr φ ψ φ.iod * chr φ ψ φ.iod = 1 := by
    rw [← map_mul]
    have e : φ.iod * φ.iod = 1 := by
      simp only [Frame.iod]
      ext <;> simp
    rw [e, map_one]
  have hv : (chr φ ψ φ.iod : ℂ) * (chr φ ψ φ.iod : ℂ) = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hv with h1 | h1
  · left
    refine ⟨⟨hT, Units.ext (by simpa using h1)⟩, ?_⟩
    intro hK
    apply hk
    simpa [keptA] using hK
  · right
    exact ⟨hT, Units.ext (by simpa using h1)⟩

theorem UpperTheory.Comparison₂.sigA_le :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤ 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
  intro Λ φ H TT x eps C ell hx hE hell
  classical
  unfold SigA
  have hb : ∀ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw,
      ‖GPsi (arith H.toHostRaw) ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) := by
    intro ψ hψ
    rw [Finset.mem_sdiff] at hψ
    rw [(prim_read φ H ell hell ψ).2 x]
    exact hE.bdG _ (chr_bounded Λ φ H.toHostRaw ψ hψ.1 hψ.2) _ _ (HostRaw.isPrimOf_prim _ _)
  calc _ ≤ ∑ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw, x ^ ((1 : ℝ) / 2 + eps) := Finset.sum_le_sum hb
    _ = ((PsiA φ.A0 \ keptA Λ H.toHostRaw).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((PsiA φ.A0).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ = 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [card_PsiA, hE.o_eq]
        push_cast
        ring
