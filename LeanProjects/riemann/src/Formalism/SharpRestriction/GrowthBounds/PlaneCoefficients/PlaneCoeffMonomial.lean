import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Comm

variable {σ τ Kf : Type} [Field Kf]

theorem oneT_monomial (e : Module.End Kf (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) (q : MvPolynomial τ Kf) :
    oneT e (monomial mo q) = monomial mo (e q) := by
  unfold oneT
  by_cases hq : q = 0
  · simp [hq]
  · rw [support_monomial, if_neg hq, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem planeCoeff_monomial (nu : τ →₀ ℕ) (mo : σ →₀ ℕ) (q : MvPolynomial τ Kf) :
    planeCoeff nu (monomial mo q) = monomial mo (q.coeff nu) := by
  unfold planeCoeff
  by_cases hq : q = 0
  · simp [hq]
  · rw [support_monomial, if_neg hq, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem X_mul_monomial' {R : Type} [CommSemiring R] (v : σ) (u : σ →₀ ℕ) (a : R) :
    (X v : MvPolynomial σ R) * monomial u a = monomial (Finsupp.single v 1 + u) a := by
  rw [X, monomial_mul, one_mul]

theorem oneT_pderiv (e : Module.End Kf (MvPolynomial τ Kf)) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (pderiv v G) = pderiv v (oneT e G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, oneT_monomial, oneT_monomial, pderiv_monomial, ← nsmul_eq_mul', ← nsmul_eq_mul', map_nsmul]
  | add p q hp hq => simp only [map_add, oneT_add, hp, hq]

theorem oneT_X_mul (e : Module.End Kf (MvPolynomial τ Kf)) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (X v * G) = X v * oneT e G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [X_mul_monomial', oneT_monomial, oneT_monomial, X_mul_monomial']
  | add p q hp hq => simp only [mul_add, oneT_add, hp, hq]

theorem planeCoeff_pderiv (nu : τ →₀ ℕ) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (pderiv v G) = pderiv v (planeCoeff nu G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [pderiv_monomial, planeCoeff_monomial, planeCoeff_monomial, pderiv_monomial, ← nsmul_eq_mul', ← nsmul_eq_mul',
      coeff_smul]
  | add p q hp hq => simp only [map_add, planeCoeff_add, hp, hq]

theorem planeCoeff_X_mul (nu : τ →₀ ℕ) (v : σ) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    planeCoeff nu (X v * G) = X v * planeCoeff nu G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [X_mul_monomial', planeCoeff_monomial, planeCoeff_monomial, X_mul_monomial']
  | add p q hp hq => simp only [mul_add, planeCoeff_add, hp, hq]

theorem oneT_oneT (e T : Module.End Kf (MvPolynomial τ Kf)) (G : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT e (oneT T G) = oneT (e * T) G := by
  induction G using MvPolynomial.induction_on' with
  | monomial u a => rw [oneT_monomial, oneT_monomial, oneT_monomial, Module.End.mul_apply]
  | add p q hp hq => simp only [oneT_add, hp, hq]

end Comm

section XXgLin

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J) {d : TL J Dt.nL r → ℕ} {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}

theorem XXg_add {F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) (hG : XXg Dt d th thL G) :
    XXg Dt d th thL (F + G) := by
  refine ⟨Submodule.add_mem _ hF.1 hG.1, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_add]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF.2.1 rho j i) (hG.2.1 rho j i))
  · exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (hF.2.2 j mm hm) (hG.2.2 j mm hm))

theorem XXg_smul (c : KK O) {F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) :
    XXg Dt d th thL (c • F) := by
  refine ⟨Submodule.smul_mem _ c hF.1, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_smul]
    exact geZ_mono (valS_smul_ge _ _ _ _) (hF.2.1 rho j i)
  · exact geZ_mono (valS_smul_ge _ _ _ _) (hF.2.2 j mm hm)

theorem XXg_zero : XXg Dt d th thL (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j mm hm => ?_⟩
  · rw [Fdig_zero, valS_zero_eq_top]; exact geZ_top _
  · rw [valS_zero_eq_top]; exact geZ_top _

end XXgLin

theorem max_three_le_add {a b c a' b' c' t : ℝ} (ha : a ≤ a' + t) (hb : b ≤ b' + t) (hc : c ≤ c' + t) :
    max a (max b c) ≤ max a' (max b' c') + t := by
  refine max_le (le_trans ha ?_) (max_le (le_trans hb ?_) (le_trans hc ?_))
  · exact add_le_add_left (le_max_left _ _) _
  · exact add_le_add_left (le_trans (le_max_left _ _) (le_max_right _ _)) _
  · exact add_le_add_left (le_trans (le_max_right _ _) (le_max_right _ _)) _

section Th

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {J : ℕ} (nL : ZMod J → ℕ) (K : ℕ) [NeZero K]

theorem thStar_le (ka ka1 : ZMod J → ℕ → Fin K → ℤ) (j : ZMod J) (u : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (h1 : (ka j (u + 1) 0 : ℝ) ≤ ka1 j (u + 1) 0 + t) (h2 : (ka j (u - 1) 0 : ℝ) ≤ ka1 j (u - 1) 0 + t) :
    thStar Fr p deg Y k mS nL K ka j u ≤ thStar Fr p deg Y k mS nL K ka1 j u + t := by
  unfold thStar
  simp only []
  apply max_three_le_add
  · linarith
  · split_ifs <;> linarith
  · split_ifs <;> linarith

end Th

theorem touch_cost_nonneg {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (s : Fin n') (jz : ℤ) (u : ℕ) : 0 ≤ cost1 Fr s jz u := by
  unfold cost1
  split_ifs <;> norm_num

theorem touch_cost_eq_one {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (s : Fin n') (jz : ℤ) (u : ℕ) (h : touchT Fr jz u s) :
    cost1 Fr s jz u = 1 := by
  unfold cost1
  rw [if_pos h]

def thUp {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) (s : Fin n') (th : ∀ j, Fin (Dt.nch j) → ℝ) :
    ∀ j, Fin (Dt.nch j) → ℝ :=
  fun j i => th j i + cost1 Fr s (segZ j) i.val

def thLUp {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {p : ℕ} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {J : ℕ} (Dt : SignedChainData p O r J) (s : Fin n') (thL : ZMod J → Fin r → ℝ) :
    ZMod J → Fin r → ℝ :=
  fun j mm => thL j mm + cost1 Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))

section Glue

variable {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} [NeZero J] (K : ℕ) [NeZero K]
  (Dt : SignedChainData p O r J)

variable {Fr p deg Y k mS K Dt}

theorem thLe_up {sc sL : ℝ} {loss : ℤ → ℕ → ℝ} {s : Fin n'} {ka : ZMod J → ℕ → Fin K → ℤ}
    {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr s jz u) Dt ka th thL) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka (thUp Fr Dt s th) (thLUp Fr Dt s thL) := by
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have := hT.1 j i
    unfold thUp
    linarith
  · have := hT.2 j mm hm
    unfold thLUp
    linarith

theorem thLe_weak {sc sL : ℝ} {loss : ℤ → ℕ → ℝ} {s : Fin n'} {ka : ZMod J → ℕ → Fin K → ℤ}
    {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr s jz u) Dt ka th thL) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka th thL := by
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have := hT.1 j i
    have := touch_cost_nonneg Fr s (segZ j) i.val
    linarith
  · have := hT.2 j mm hm
    have := touch_cost_nonneg Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))
    linarith

theorem thLUp_pos {s : Fin n'} {thL : ZMod J → Fin r → ℝ} (h : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm) :
    ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thLUp Fr Dt s thL j mm := by
  intro j mm hm
  have := h j mm hm
  have := touch_cost_nonneg Fr s (segZ j) (Dt.nL j + (r - 1 - mm.val))
  unfold thLUp
  linarith

def TouchAt (Fr : Frames n' r) (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) : Prop :=
  ∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
      (x0 ∈ NSet Dt.nL j (u + 1) ∨ ∃ m : Fin r, x0 = ⟨j - 1, Sum.inr m⟩) →
      touchT Fr (segZ j) u (posOf n' (posTL Fr x0))

theorem thDrop_of (hB : Base Fr p Dt) {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) :
    ThDrop Dt x0 th (thUp Fr Dt (posOf n' (posTL Fr x0)) th) thL (thLUp Fr Dt (posOf n' (posTL Fr x0)) thL) := by
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
  have hr : 0 < r := NeZero.pos r
  refine ⟨fun j i => ?_, fun j i hc => ?_, fun j mm => ?_, fun j mm hx => ?_⟩
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) i.val
    unfold thUp
    linarith
  · have hi : i.val < Dt.nL j + r := by
      have := i.isLt
      have := b5 j
      omega
    have ht : touchT Fr (segZ j) i.val (posOf n' (posTL Fr x0)) := by
      apply hG j i.val hi
      rcases hc with ⟨l, hl, hmem⟩ | hw
      · left
        rw [b6 j i] at hmem
        rcases hmem with hmem | ⟨l', hl', hlt⟩
        · exact absurd hmem (by simp)
        · have : l = l' := Sum.inl.inj hl'
          subst this
          exact Or.inl ⟨l, hl, by omega⟩
      · exact Or.inr hw
    unfold thUp
    rw [touch_cost_eq_one Fr _ _ _ ht]
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) (Dt.nL j + (r - 1 - mm.val))
    unfold thLUp
    linarith
  · have hi : Dt.nL j + (r - 1 - mm.val) < Dt.nL j + r := by omega
    have ht : touchT Fr (segZ j) (Dt.nL j + (r - 1 - mm.val)) (posOf n' (posTL Fr x0)) := by
      apply hG j _ hi
      left
      rcases hx with ⟨l, hl⟩ | ⟨m', hlt, hm'⟩
      · exact Or.inl ⟨l, hl, by have := l.isLt; omega⟩
      · refine Or.inr ⟨m', hm', ?_⟩
        have h1 : mm.val < m'.val := hlt
        have h2 := m'.isLt
        omega
    unfold thLUp
    rw [touch_cost_eq_one Fr _ _ _ ht]

theorem inN_le_cost {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0) (j : ZMod J) (u u' : ℕ) (hu : u < Dt.nL j + r)
    (hu' : u' ≤ u + 1) : (inN Dt.nL x0 j u' : ℝ) ≤ cost1 Fr (posOf n' (posTL Fr x0)) (segZ j) u := by
  unfold inN
  split_ifs with h
  · rw [touch_cost_eq_one Fr _ _ _ (hG j u hu (Or.inl (NSet_mono Dt.nL j hu' h)))]
    norm_num
  · have := touch_cost_nonneg Fr (posOf n' (posTL Fr x0)) (segZ j) u
    simpa using this

theorem thLe_ka (hB : Base Fr p Dt) {x0 : TL J Dt.nL r} (hG : TouchAt Fr Dt x0) {sc sL : ℝ} {loss : ℤ → ℕ → ℝ}
    {ka ka1 : ZMod J → ℕ → Fin K → ℤ} {th : ∀ j, Fin (Dt.nch j) → ℝ} {thL : ZMod J → Fin r → ℝ}
    (hT : ThLe Fr p deg Y k mS K sc sL (fun jz u => loss jz u + cost1 Fr (posOf n' (posTL Fr x0)) jz u) Dt ka th thL)
    (hka : ∀ j u, ka j u 0 ≤ ka1 j u 0 + inN Dt.nL x0 j u) :
    ThLe Fr p deg Y k mS K sc sL loss Dt ka1 th thL := by
  have hr : 0 < r := NeZero.pos r
  have key : ∀ (j : ZMod J) (u : ℕ), u < Dt.nL j + r →
      thStar Fr p deg Y k mS Dt.nL K ka j u ≤
        thStar Fr p deg Y k mS Dt.nL K ka1 j u + cost1 Fr (posOf n' (posTL Fr x0)) (segZ j) u := by
    intro j u hu
    apply thStar_le _ _ _ _ _ _ _ _ _ _ _ _ _ (touch_cost_nonneg _ _ _ _)
    · have h1 : ((ka j (u + 1) 0 : ℤ) : ℝ) ≤ ((ka1 j (u + 1) 0 + inN Dt.nL x0 j (u + 1) : ℤ) : ℝ) := by
        exact_mod_cast hka j (u + 1)
      have h2 := inN_le_cost hG j u (u + 1) hu le_rfl
      push_cast at h1
      linarith
    · have h1 : ((ka j (u - 1) 0 : ℤ) : ℝ) ≤ ((ka1 j (u - 1) 0 + inN Dt.nL x0 j (u - 1) : ℤ) : ℝ) := by
        exact_mod_cast hka j (u - 1)
      have h2 := inN_le_cost hG j u (u - 1) hu (by omega)
      push_cast at h1
      linarith
  refine ⟨fun j i => ?_, fun j mm hm => ?_⟩
  · have hi : i.val < Dt.nL j + r := by
      have := i.isLt
      have := hB.2.2.2.2.1 j
      omega
    have := hT.1 j i
    have := key j i.val hi
    linarith
  · have := hT.2 j mm hm
    have := key j (Dt.nL j + (r - 1 - mm.val)) (by omega)
    linarith

end Glue

end Formalism.MainNotions.PairMembershipBlocks
