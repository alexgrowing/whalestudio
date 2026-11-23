import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

attribute [local instance] borelH

namespace DiscreteGroups.T1.G

def CutTail2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (r₀ r₁ ε : ℝ),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ C'₀ : ℝ, ∀ C' : ℝ, C'₀ ≤ C' → ∃ C : ℝ,
  ∀ (k : ℕ) (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → D4.IsTest2J (trM Φ M) (r₀ + k * r₁) →
    ‖∫ x, lInt D k₁ k₂ (C' * ((1 + k) * (1 + r₀ + r₁))) Uπ x ∂D.ν - ∫ x, lInt0 D k₁ k₂ Uπ x ∂D.ν‖ ≤ C * ‖U‖ * ε ^ k

theorem growth_of_ellipticFormula (hE : D4.EllFormula2J) (hS : SFun) (hD : DomOne) (hK : KerSplit) (hU : UncutHalf)
    (hT : CutTail2) : GrowthPiJ := by
  intro E _ _ _ _ n hn _ _ _ _ μ₁ _ μ₂ _
  obtain ⟨F₁, F₂, D, h₁, h₂, hcut, hmu⟩ := hD E n μ₁ μ₂
  refine ⟨D, hmu, ?_⟩
  intro π hπ ι _ Φ₁ Φ₂ T₁ T₂ M r₀ r₁ ε a1 a2 hfin b1 b2 hr₀ hr₁ hε
  obtain ⟨C₀, hC₀, hell⟩ := hE E n 0
  obtain ⟨k₁, k₂, hv, C, N, hb⟩ := hS E n 0 D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨C'₀, hT'⟩ := hT E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  obtain ⟨Ct, hCt⟩ := hT' (max C₀ C'₀) (le_max_right _ _)
  have hC'0 : 0 ≤ max C₀ C'₀ := le_trans hC₀ (le_max_left _ _)
  refine ⟨max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct|, N, fun k U Φ t c1 c2 hU1 hU2 c3 ht => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : 0 ≤ r₀ + k * r₁ := by positivity
  have hg : 1 + (r₀ + k * r₁) ≤ (1 + k) * (1 + r₀ + r₁) := by
    nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hτ0 : 0 ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) := by positivity
  have hτC : C₀ * (1 + (r₀ + k * r₁)) ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) :=
    mul_le_mul (le_max_left _ _) hg (by positivity) hC'0
  have e1 : ellSum2 μ₁ μ₂ (trM Φ M) = ∫ x, lInt D k₁ k₂ (max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) U x ∂D.ν := by
    rw [← hell μ₁ μ₂ F₁ F₂ _ _ _ h₁ h₂ c3 hr hτC, ← hcut]
    exact (hb _ hτ0 U).2.2 Φ c1 c2
  obtain ⟨Uπ, hpi, -, hsplit⟩ := hK E n D π ι k₁ k₂ _ C N (fun V => ⟨(hb _ hτ0 V).1, (hb _ hτ0 V).2.1⟩) U hU1 hU2
  obtain ⟨-, hhalf⟩ := hU E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  have htail := hCt k U Uπ Φ c1 c2 hpi c3
  rw [e1, ← hhalf]
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hsplit htail).trans (add_le_add ?_ ?_))
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc C * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N
        ≤ |C| * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + max C₀ C'₀ * (1 + r₀ + r₁)) * (1 + k)) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (abs_nonneg C)
          nlinarith [mul_nonneg hC'0 hk]
      _ = |C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N * (1 + k) ^ N := by rw [mul_pow, mul_assoc]
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (1 + k) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have h1 : Ct ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| := (le_abs_self Ct).trans (le_max_right _ _)
    have h0 : 0 ≤ ‖U‖ * ε ^ k := by positivity
    calc Ct * ‖U‖ * ε ^ k = Ct * (‖U‖ * ε ^ k) := by ring
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (‖U‖ * ε ^ k) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring

end DiscreteGroups.T1.G

end
