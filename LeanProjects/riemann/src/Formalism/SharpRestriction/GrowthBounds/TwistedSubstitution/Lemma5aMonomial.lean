import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

theorem symP_eq_sum (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K)
    (hrk : r ≤ m + 1) (F : Frames n' r) (c' Q : ℕ) (P : RRing O n' (r + K)) :
    symP p O hk hrk F c' Q P = ∑ ga ∈ (SPR O p F hrk c' Q).support,
      algebraMap O (KK O) ((SPR O p F hrk c' Q).coeff ga) •
        MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) P * monomial ga 1) := by
  unfold symP
  conv_lhs => rw [(SPR O p F hrk c' Q).as_sum]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun ga _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, ← MvPolynomial.map_C, ← map_mul]
  congr 1
  rw [show (monomial ga) ((SPR O p F hrk c' Q).coeff ga) = C ((SPR O p F hrk c' Q).coeff ga) * monomial ga 1 by
    rw [C_mul_monomial, mul_one]]
  ring

def Lemma5aMonomialAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ b, ∀ ga ∈ (SPR O p F hrk (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)).support,
      MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
        (MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (B b) * monomial ga 1))

theorem conclusionAt_of_monomialAt (C CLa : ℝ) (h : Lemma5aMonomialAt C CLa) : Lemma5aAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD b
  rw [symP_eq_sum]
  refine Submodule.sum_mem (memSub 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
    (cPrime n' r TT.card c0 cpp cStar)) fun ga hga => Submodule.smul_mem _ _ ?_
  exact h p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD b ga hga

def Lemma5aMonomial (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → Lemma5aMonomialAt C CLa

theorem lemma5a_of_monomial (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : Lemma5aMonomial D CLa Ck Crk Cdeg) :
    Lemma5aTheoremII D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h2⟩ := h hA
  exact ⟨C₁, h1, fun C hC => conclusionAt_of_monomialAt C CLa (h2 C hC)⟩

end Formalism.MainNotions.TestSideWords
