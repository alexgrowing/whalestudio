import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula

namespace GlobalTheory.MultinomCoeff

theorem mono_apply {σ : Type} [DecidableEq σ] (T : Finset σ) (x : σ) :
    mono T x = if x ∈ T then 1 else 0 := by
  unfold mono
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

theorem mono_sub_single {σ : Type} [DecidableEq σ] (T : Finset σ) (s : σ) (hs : s ∈ T) :
    mono T - Finsupp.single s 1 = mono (T.erase s) := by
  ext x
  rw [Finsupp.tsub_apply, mono_apply, mono_apply, Finsupp.single_apply]
  by_cases hx : x = s
  · subst hx; simp [hs]
  · simp [Finset.mem_erase, hx, Ne.symm hx]

theorem mem_support_mono {σ : Type} [DecidableEq σ] (T : Finset σ) (s : σ) :
    s ∈ (mono T).support ↔ s ∈ T := by
  rw [Finsupp.mem_support_iff, mono_apply]; split_ifs with h <;> simp [h]

theorem coeff_mono_X_mul {σ : Type} [DecidableEq σ] (T : Finset σ) (s : σ) (ω : MvPolynomial σ ℝ) :
    coeff (mono T) (X s * ω) = if s ∈ T then coeff (mono (T.erase s)) ω else 0 := by
  rw [coeff_X_mul']
  by_cases h : s ∈ T
  · rw [if_pos ((mem_support_mono T s).2 h), if_pos h, mono_sub_single T s h]
  · rw [if_neg (fun h' => h ((mem_support_mono T s).1 h')), if_neg h]

theorem sum_powersetCard_insert {σ : Type} [DecidableEq σ] (A : Finset σ) (k : ℕ) (f : Finset σ → ℝ) :
    ∑ U ∈ A.powersetCard k, ∑ s ∈ A \ U, f (insert s U)
      = ((k:ℝ) + 1) * ∑ V ∈ A.powersetCard (k+1), f V := by
  have hR : ((k:ℝ) + 1) * ∑ V ∈ A.powersetCard (k+1), f V
      = ∑ V ∈ A.powersetCard (k+1), ∑ s ∈ V, f (insert s (V.erase s)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun V hV => ?_
    have hc := (Finset.mem_powersetCard.1 hV).2
    rw [Finset.sum_congr rfl fun s hs => by rw [Finset.insert_erase hs]]
    rw [Finset.sum_const, hc, nsmul_eq_mul]; push_cast; ring
  rw [hR, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨insert p.2 p.1, p.2⟩) (fun p _ => ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨U, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at h ⊢
    obtain ⟨⟨hU, hk⟩, hsA, hsU⟩ := h
    refine ⟨⟨Finset.insert_subset hsA hU, ?_⟩, Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hsU, hk]
  · rintro ⟨V, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at h ⊢
    obtain ⟨⟨hV, hk⟩, hsV⟩ := h
    refine ⟨⟨(Finset.erase_subset _ _).trans hV, ?_⟩, hV hsV, Finset.notMem_erase _ _⟩
    rw [Finset.card_erase_of_mem hsV, hk]; rfl
  · rintro ⟨U, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at h
    simp [Finset.erase_insert h.2.2]
  · rintro ⟨V, s⟩ h
    simp only [Finset.mem_sigma] at h
    simp [Finset.insert_erase h.2]
  · rintro ⟨U, s⟩ h
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at h
    simp [Finset.erase_insert h.2.2]

theorem coeff_mono_sum_pow_mul {σ : Type} [DecidableEq σ] (C R : Finset σ) (k : ℕ) (ω : MvPolynomial σ ℝ) :
    coeff (mono R) ((∑ s ∈ C, X s) ^ k * ω)
      = (k.factorial : ℝ) * ∑ U ∈ (R ∩ C).powersetCard k, coeff (mono (R \ U)) ω := by
  induction k generalizing ω with
  | zero => simp
  | succ k ih =>
    have hin : ∀ U ∈ (R ∩ C).powersetCard k,
        coeff (mono (R \ U)) ((∑ s ∈ C, X s) * ω)
          = ∑ s ∈ (R ∩ C) \ U, coeff (mono (R \ insert s U)) ω := by
      intro U _
      rw [Finset.sum_mul, coeff_sum]
      simp_rw [coeff_mono_X_mul]
      rw [Finset.sum_ite_mem]
      have : C ∩ (R \ U) = (R ∩ C) \ U := by
        ext x; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
      rw [this]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sdiff_insert]
    rw [pow_succ, mul_assoc, ih, Finset.sum_congr rfl hin,
      sum_powersetCard_insert (R ∩ C) k (fun V => coeff (mono (R \ V)) ω), Nat.factorial_succ]
    push_cast; ring

end GlobalTheory.MultinomCoeff
