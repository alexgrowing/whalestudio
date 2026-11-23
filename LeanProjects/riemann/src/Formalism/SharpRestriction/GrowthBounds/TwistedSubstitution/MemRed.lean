import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemLin

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

def Lemma5aAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ b, MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
      (symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b))

def WordConditionAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ Fp : MvPolynomial (TV n' (m + 1)) (KK O),
      MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
        (cPrime n' r TT.card c0 cpp cStar) Fp →
      ∀ l : List (Fin n' × (Fin (m + 1) × Fin (m + 1))), (∀ z ∈ l, z.1 ∈ TT) →
        (∀ s, (l.filter fun z => z.1 = s).length ≤ c0) →
        MemAtG (1 / 8) (3 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
          (cPrime n' r TT.card c0 cpp cStar) (opWord l Fp)

theorem memAt_of_wordConditionAt (C CLa : ℝ) (h5 : Lemma5aAt C CLa) (hW : WordConditionAt C CLa) : MemStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD G hG
  rw [memAt_iff]
  have hM : ∀ f ∈ Submodule.span (KK O) (Set.range fun b =>
      symP p O hk hrk F (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)),
      MemAtG 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x)
        (cPrime n' r TT.card c0 cpp cStar) f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact h5 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD b
    | zero => exact memAtG_zero _ _ _ _ _ _ _ _ _ _ _
    | add y z _ _ hy hz => exact memAtG_add _ _ _ _ _ _ _ _ _ _ _ hy hz
    | smul c y _ hy => exact memAtG_smul _ _ _ _ _ _ _ _ _ _ _ c hy
  unfold OpCl at hG
  induction hG using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, l, h1, h2, rfl⟩ := hy
    exact hW p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD f (hM f hf)
      l h1 h2
  | zero => exact memAtG_zero _ _ _ _ _ _ _ _ _ _ _
  | add y z _ _ hy hz => exact memAtG_add _ _ _ _ _ _ _ _ _ _ _ hy hz
  | smul c y _ hy => exact memAtG_smul _ _ _ _ _ _ _ _ _ _ _ c hy

def Lemma5aTheoremII (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → Lemma5aAt C CLa

def RestWord (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → WordConditionAt C CLa

theorem memCondition_of_theoremII (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h5 : Lemma5aTheoremII D CLa Ck Crk Cdeg)
    (hW : RestWord D CLa Ck Crk Cdeg) : RestMEM D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h5'⟩ := h5 hA
  obtain ⟨C₂, _, hW'⟩ := hW hA
  refine ⟨max C₁ C₂, lt_max_of_lt_left h1, fun C hC => ?_⟩
  exact memAt_of_wordConditionAt C CLa (h5' C (le_trans (le_max_left _ _) hC)) (hW' C (le_trans (le_max_right _ _) hC))

end Formalism.MainNotions.TestSideWords
