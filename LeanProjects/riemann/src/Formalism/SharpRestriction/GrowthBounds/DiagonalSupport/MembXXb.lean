import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ThresholdGeOddPosition

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace XXb

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)

def Mx (j : ZMod J) (x : ℤ) : ℤ :=
  if h : ∃ u, u < Dt.nL j + r ∧ pU p O Fr Dt j u = x then
    (if Even x then ka j (Classical.choose h + 1) 0 + 4 * (cP : ℤ) else ka j (Classical.choose h) 0 + 4 * (cP : ℤ))
  else 0

theorem Mx_even {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j (u + 1) 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dif_pos hex, if_pos he, heq]

theorem Mx_odd {L₁ N₁' : ℕ} (hV : Fr.Valid L₁ N₁') (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < Dt.nL j + r) (he : ¬ Even (pU p O Fr Dt j u)) :
    Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) = ka j u 0 + 4 * (cP : ℤ) := by
  have hinj : ∀ a b, a < Dt.nL j + r → b < Dt.nL j + r → pU p O Fr Dt j a = pU p O Fr Dt j b → a = b := by
    intro a b ha hb hab
    unfold pU at hab
    rw [hnL j] at ha hb hab
    rcases lt_trichotomy a b with h1 | h1 | h1
    · exact absurd hab (ne_of_lt ((posU_lt_iff hV (segZ j) a b ha hb).mpr h1))
    · exact h1
    · exact absurd hab (ne_of_gt ((posU_lt_iff hV (segZ j) b a hb ha).mpr h1))
  have hex : ∃ u', u' < Dt.nL j + r ∧ pU p O Fr Dt j u' = pU p O Fr Dt j u := ⟨u, hu, rfl⟩
  have hc := Classical.choose_spec hex
  have heq : Classical.choose hex = u := hinj _ _ hc.1 hu hc.2
  unfold Mx
  rw [dif_pos hex, if_neg he, heq]

theorem cond_at {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {d : Fin n' → ℕ}
    (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O)
    (hPl : PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A) (hNo : NoOK p O Fr cP Dt dNo ka j B) (u : ℕ)
    (hu : u < Dt.nL j + r) (hx : pU p O Fr Dt j u ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) (pU p O Fr Dt j u)) :
    (Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y < pU p O Fr Dt j u} A) ∧
    (¬ Even (pU p O Fr Dt j u) →
      lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) : ℤ) : WithBot ℤ) ∧
      ((Mx p O Fr cP Dt ka j (pU p O Fr Dt j u) + (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ) : ℤ) : WithTop ℤ) ≤
        valS LZ {y | y ≤ pU p O Fr Dt j u} A) ∧
    geR (valS LZ {y | y < pU p O Fr Dt j u} A)
      (Bo p Fr deg (segZ j) (pU p O Fr Dt j u) / 2 - sl p Fr deg Y (r + K) (segZ j) (pU p O Fr Dt j u)) := by
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hc0 : (0 : ℝ) ≤ (cP : ℝ) := Nat.cast_nonneg _
  have hs : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j u := hM.margin (segZ j) _ hx hW
  refine ⟨fun he => ?_, fun he => ?_, ?_⟩
  · rw [Mx_even p O Fr cP Dt ka hV hnL j u hu he]
    refine ⟨(hNo.2.2 u hu).2, int_le_val ?_ (hPl.2.2.1 u hu)⟩
    have h1 := threshold_ge_even_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs
    unfold tauU
    push_cast
    exact h2
  · rw [Mx_odd p O Fr cP Dt ka hV hnL j u hu he]
    have huN : u < Dt.nL j := by
      by_contra hcon
      exact he (posU_even hV (segZ j) (Dt.nL j) u (by omega) hu)
    refine ⟨(hNo.2.2 u hu).1, int_le_val ?_ (hPl.2.2.2 u huN)⟩
    obtain ⟨l1, l2⟩ := posU_letter hV hr1 (segZ j) (Dt.nL j) (hnL j) (u + 1) (by omega)
    have hs' : 128 * (cP : ℝ) ≤ slU Fr p deg Y (r + K) Dt.nL j (u + 1) := hM.margin (segZ j) _ l1 l2
    have h1 := threshold_ge_odd_position Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u he
    have h2 := ar1 _ _ _ _ _ h1 hs'
    unfold tauU
    push_cast
    exact h2
  · refine geR_of_ceil ?_ (hPl.2.2.1 u hu)
    have h1 := th_ge_B Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u
    exact ar3 _ _ _ _ h1 hs hc0

end At

end XXb

open XXb in

theorem restXXG_b : RestXXG := by
  intro p _ n' r K _ _ _ O _ _ _ S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka hT δ j A B hPl hNo
  have hV := hM.frames.2.1
  have hr1 : 1 ≤ r := by have := hM.two_le_r; omega
  have hnL := hT.1.2.1
  have hdeg : ∀ mm ∈ (plEmb O r K A * nmEmb O r K B).support, ∀ x,
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x) ∧
      ordDeg mm x ≤ δ (j, x) + dNoOf p O Fr Dt dNo (j, x) := by
    intro mm hmm x
    obtain ⟨ua, hua, ub, hub, h⟩ := deg_mul A B mm hmm
    have e1 : ∑ c : Fin r, mm (x, Fin.castAdd K c) = δ (j, x) := by
      rw [← hPl.2.1 ua hua x]
      exact Finset.sum_congr rfl fun c _ => (h x).1 c
    have e2 : ∑ c : Fin K, mm (x, Fin.natAdd r c) = dNoOf p O Fr Dt dNo (j, x) := by
      rw [← hNo.2.1 ub hub x]
      exact Finset.sum_congr rfl fun c _ => (h x).2 c
    refine ⟨by rw [Fin.sum_univ_add, e1, e2], ?_⟩
    unfold ordDeg
    split_ifs
    · rw [e2]; omega
    · rw [e1]; omega
  refine ⟨?_, ?_⟩
  · unfold XX'
    refine Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨A, B, Mx p O Fr cP Dt ka j, hPl.1, hNo.1, ?_, rfl⟩, ?_⟩
    · intro x hx hW
      obtain ⟨u, hu, rfl⟩ := exists_posU hV hr1 (segZ j) (Dt.nL j) (hnL j) x hx hW
      exact cond_at p O Fr deg Y N₁ G' cP Dt dNo ka hM hnL δ j A B hPl hNo u hu hx hW
    · rw [mem_restrictSupport_iff]
      intro mm hmm x _ _
      show (ordDeg mm x : ℝ) ≤ ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)
      exact Nat.cast_le.2 (hdeg mm hmm x).2
  · rw [mem_restrictSupport_iff]
    intro mm hmm x _
    exact (hdeg mm hmm x).1

end Formalism.MainNotions.Proposition5Numerics
