import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

section TieD

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def TwistedSubstitutionDegreeBound (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ)
    (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  Dt.d = dPl ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val}) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.th j i = thStar Fr p deg Y k mS Dt.nL K ka j i.val -
    sc * slU Fr p deg Y k Dt.nL j i.val - loss (segZ j) i.val) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    Dt.thL j mm = thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      sL * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val)) - loss (segZ j) (Dt.nL j + (r - 1 - mm.val))

end TieD

def MemAtD (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionDegreeBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL loss Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

section Mono

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)

theorem geZ_anti {x : WithTop ℤ} {t t' : ℝ} (h : t' ≤ t) (hx : geZ x t) : geZ x t' := by
  intro k hk
  exact h.trans (hx k hk)

end Mono

section TieLe

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def TwistedSubstitutionLossInequality (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ)
    (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  Dt.d = dPl ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val}) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.th j i ≤ thStar Fr p deg Y k mS Dt.nL K ka j i.val -
    sc * slU Fr p deg Y k Dt.nL j i.val - loss (segZ j) i.val) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    Dt.thL j mm ≤ thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      sL * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val)) - loss (segZ j) (Dt.nL j + (r - 1 - mm.val))

end TieLe

def MemAtLe (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionLossInequality Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL loss Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

section LeMono

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)

theorem memAtG_of_le (sc sL : ℝ) (F : MvPolynomial (TV n' (m + 1)) (KK O))
    (h : MemAtLe sc sL (fun _ _ => 0) p O hk Fr deg Y N₁ G' cP F) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hT
  exact h J Dt dPl dNo ka ⟨h1, h2, h3, h4, h5, h6, h7, fun j i => by rw [h8 j i]; simp,
    fun j mm hmm => by rw [h9 j mm hmm]; simp⟩ rho e he nu

theorem memAtLe_mono (sc sL sc' sL' : ℝ) (loss loss' : ℤ → ℕ → ℝ)
    (hch : ∀ (jz : ℤ) (u : ℕ), u ≤ (Fr.LLset jz).card →
      sc * (sl p Fr deg Y (r + K) jz (posU Fr (Fr.LLset jz).card jz u) : ℝ) + loss jz u ≤
        sc' * (sl p Fr deg Y (r + K) jz (posU Fr (Fr.LLset jz).card jz u) : ℝ) + loss' jz u)
    (hl : ∀ (jz : ℤ) (u : ℕ), (Fr.LLset jz).card < u → u < (Fr.LLset jz).card + r →
      sL * (sl p Fr deg Y (r + K) jz (posU Fr (Fr.LLset jz).card jz u) : ℝ) + loss jz u ≤
        sL' * (sl p Fr deg Y (r + K) jz (posU Fr (Fr.LLset jz).card jz u) : ℝ) + loss' jz u)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) (hF : MemAtLe sc sL loss p O hk Fr deg Y N₁ G' cP F) :
    MemAtLe sc' sL' loss' p O hk Fr deg Y N₁ G' cP F := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hT
  refine hF J Dt dPl dNo ka ⟨h1, h2, h3, h4, h5, h6, h7, fun j i => ?_, fun j mm hmm => ?_⟩ rho e he nu
  · have hi : i.val < Dt.nL j + 1 := by
      have h := i.isLt
      have := h6 j
      omega
    have hc := hch (segZ j) i.val (by rw [← h2 j]; omega)
    have e1 : slU Fr p deg Y (r + K) Dt.nL j i.val =
        (sl p Fr deg Y (r + K) (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) i.val) : ℝ) := by
      simp only [slU, h2 j]
    have := h8 j i
    rw [e1] at this ⊢
    linarith
  · have hc := hl (segZ j) (Dt.nL j + (r - 1 - mm.val)) (by rw [← h2 j]; omega) (by rw [← h2 j]; omega)
    have e1 : slU Fr p deg Y (r + K) Dt.nL j (Dt.nL j + (r - 1 - mm.val)) =
        (sl p Fr deg Y (r + K) (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j)
          (Dt.nL j + (r - 1 - mm.val))) : ℝ) := by
      simp only [slU, h2 j]
    have := h9 j mm hmm
    rw [e1] at this ⊢
    linarith

end LeMono

end Formalism.MainNotions.TestSideWords
