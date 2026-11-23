import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def aS (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (s : ℝ) : H E n 0 := (splitCentre E n s, 1)

open GlobalTheory.CuspRep.CuspidalL2GL in
theorem aS_add (s t : ℝ) : aS E n (s + t) = aS E n s * aS E n t :=
  Prod.ext (splitCentre_add s t) (mul_one _).symm

def G2 {ι : Type} [Fintype ι] (D : Dom E n 0) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D)
    (V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x z : H E n 0) : ℂ :=
  ∑ i, inner ℂ (k₁ x i) (V (k₂ z i))

def AvgInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (L : H E n 0 → ℂ), (∀ (γ : ratH E n 0) x, L ((γ : H E n 0) * x) = L x) → Continuous L → Integrable L D.ν →
  ∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s : ℝ, w s = 1 →
    Integrable (fun x => w (ldet x) * ∫ s : ℝ, L (x * aS E n s)) D.ν ∧
      ∫ x, L x ∂D.ν = (ldet (aS E n 1) : ℂ) * ∫ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) ∂D.ν

def KerEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ →
    (∀ (γ : ratH E n 0) x, lInt0 D k₁ k₂ Uπ ((γ : H E n 0) * x) = lInt0 D k₁ k₂ Uπ x) ∧
      ∀ s x z, G2 D k₁ k₂ Uπ (x * aS E n s) (z * aS E n (-s)) = G2 D k₁ k₂ Uπ x z

def TwTrK : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ →
  ∀ (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)) (t : ℂ), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → IsTwTr D.μ π (trM Φ M) t →
    Integrable (lInt0 D k₁ k₂ Uπ) D.ν ∧ ∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s : ℝ, w s = 1 →
      (ldet (aS E n 1) : ℂ) * ∫ x, w (ldet x) * (∫ s : ℝ, G2 D k₁ k₂ Uπ (x * aS E n s) x) ∂D.ν = t

theorem exists_bump_one : ∃ w : ℝ → ℂ, Continuous w ∧ HasCompactSupport w ∧ ∫ s : ℝ, w s = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun s => ((f.normed volume s : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous_normed,
    f.hasCompactSupport_normed.comp_left Complex.ofReal_zero, ?_⟩
  rw [integral_complex_ofReal, f.integral_normed]
  simp

theorem uncutHalf_of (hA : AvgInt) (hK : KerEquiv) (hT : TwTrK) : UncutHalf := by
  intro E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  obtain ⟨hL, hG⟩ := hK E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ c1 c2 hpi
  obtain ⟨hint, htr⟩ := hT E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  refine ⟨hint, ?_⟩
  obtain ⟨w, wc, ws, w1⟩ := exists_bump_one
  have hc : Continuous (lInt0 D k₁ k₂ Uπ) := by
    unfold lInt0
    exact continuous_finset_sum _ fun i _ => ((hv.cont i).1).inner (Uπ.continuous.comp (hv.cont i).2)
  have e := (hA E n hn D _ hL hc hint w wc ws w1).2
  have hs : ∀ x, ∫ s : ℝ, lInt0 D k₁ k₂ Uπ (x * aS E n s) =
      (1 / 2 : ℂ) * ∫ s : ℝ, G2 D k₁ k₂ Uπ (x * aS E n s) x := by
    intro x
    have h1 : ∀ s, lInt0 D k₁ k₂ Uπ (x * aS E n s) = G2 D k₁ k₂ Uπ (x * aS E n (2 * s)) x := by
      intro s
      have h := hG (-s) (x * aS E n (2 * s)) x
      rw [mul_assoc, ← aS_add, neg_neg, show 2 * s + -s = s by ring] at h
      exact h
    simp_rw [h1]
    rw [Measure.integral_comp_mul_left (fun s => G2 D k₁ k₂ Uπ (x * aS E n s) x) 2,
      abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul]
    push_cast
    ring
  rw [e]
  simp_rw [hs]
  have h3 : ∀ x, w (ldet x) * ((1 / 2 : ℂ) * ∫ s : ℝ, G2 D k₁ k₂ Uπ (x * aS E n s) x) =
      (1 / 2 : ℂ) * (w (ldet x) * ∫ s : ℝ, G2 D k₁ k₂ Uπ (x * aS E n s) x) := fun x => by ring
  simp_rw [h3, integral_const_mul]
  rw [← htr w wc ws w1]
  ring

end DiscreteGroups.T1.G

end
