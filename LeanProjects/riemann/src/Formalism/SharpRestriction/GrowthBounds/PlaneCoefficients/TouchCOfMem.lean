import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DigOKAddInl

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)

theorem Pof_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) : Pof Dt (⟨j0, Sum.inl l⟩, a0) = 1 := rfl

theorem Pof_inr (j0 : ZMod J) (m0 a0 : Fin r) : Pof Dt (⟨j0, Sum.inr m0⟩, a0) = Dt.P j0 m0 := rfl

private theorem X_mul_monomialPlaneCoefficients {σ R : Type} [CommSemiring R] (w : σ) (mo : σ →₀ ℕ) (c : R) :
    (X w : MvPolynomial σ R) * monomial mo c = monomial (Finsupp.single w 1 + mo) c := by
  rw [monomial_single_add, pow_one]

private theorem liftMon_apply_liftVar (mo : TL J Dt.nL r × Fin r →₀ ℕ) (w : TL J Dt.nL r × Fin r) :
    liftMon Dt mo (Dt.liftVar w) = mo w / Pof Dt w := by
  unfold liftMon
  rw [Finsupp.mapDomain_apply (liftVar_inj Dt)]
  simp [liftE, Finsupp.onFinset_apply]

private theorem liftMon_eq_add_single_of_eq_off (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) (d : ℕ)
    (h1 : ∀ w, w ≠ v → mo' w = mo w) (h2 : mo' v / Pof Dt v = mo v / Pof Dt v + d) :
    liftMon Dt mo' = liftMon Dt mo + Finsupp.single (Dt.liftVar v) d := by
  unfold liftMon
  rw [← Finsupp.mapDomain_single, ← Finsupp.mapDomain_add]
  congr 1
  ext w
  simp only [liftE, Finsupp.onFinset_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with hw
  · subst hw
    exact h2
  · rw [h1 w (Ne.symm hw), add_zero]

private theorem digOK_iff_of_eq_off_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r)
    (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ)
    (h1 : ∀ w, w ≠ (⟨j0, Sum.inl l⟩, a0) → mo' w = mo w) :
    Dt.digOK rho mo' ↔ Dt.digOK rho mo := by
  unfold SignedChainData.digOK
  refine forall_congr' fun j => forall_congr' fun m => forall_congr' fun a => ?_
  rw [h1]
  intro h
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨⟨rfl, h⟩, -⟩ := h
  simp at h

theorem Fdig_mul_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inl l⟩, a0) * H) = X (Dt.liftVar (⟨j0, Sum.inl l⟩, a0)) * Dt.Fdig rho H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w
          = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    by_cases hd : Dt.digOK rho mo
    · rw [if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, X_mul_monomialPlaneCoefficients,
        liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by simp [Pof_inl, add_comm]), add_comm]
    · rw [if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, mul_zero]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]

private theorem inr_pair_ne_of_ne {j j0 : ZMod J} {m m0 a a0 : Fin r} (hk : ((j, m), a) ≠ ((j0, m0), a0)) :
    ((⟨j, Sum.inr m⟩, a) : TL J Dt.nL r × Fin r) ≠ (⟨j0, Sum.inr m0⟩, a0) := by
  intro he
  apply hk
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at he
  obtain ⟨⟨rfl, he⟩, rfl⟩ := he
  simp at he
  subst he
  rfl

private theorem digOK_iff_update_of_eq_off_inr (j0 : ZMod J) (m0 a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) (x : ℕ)
    (mo mo' : TL J Dt.nL r × Fin r →₀ ℕ)
    (h1 : ∀ w, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) → mo' w = mo w)
    (h2 : mo' (⟨j0, Sum.inr m0⟩, a0) % Dt.P j0 m0 = rho ((j0, m0), a0) ↔
      mo (⟨j0, Sum.inr m0⟩, a0) % Dt.P j0 m0 = x) :
    Dt.digOK rho mo' ↔ Dt.digOK (Function.update rho ((j0, m0), a0) x) mo := by
  unfold SignedChainData.digOK
  constructor
  · intro h j m a
    by_cases hk : ((j, m), a) = ((j0, m0), a0)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
      rw [Function.update_self]
      exact h2.1 (h _ _ _)
    · rw [Function.update_of_ne hk, ← h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]
      exact h j m a
  · intro h j m a
    by_cases hk : ((j, m), a) = ((j0, m0), a0)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
      have h3 := h j m a
      rw [Function.update_self] at h3
      exact h2.2 h3
    · have h3 := h j m a
      rw [Function.update_of_ne hk] at h3
      rw [h1 _ (inr_pair_ne_of_ne (Dt := Dt) hk)]
      exact h3

private theorem one_add_mod_div_cases (a P : ℕ) (hP : 0 < P) :
    (a % P + 1 < P ∧ (1 + a) % P = a % P + 1 ∧ (1 + a) / P = a / P) ∨
    (a % P + 1 = P ∧ (1 + a) % P = 0 ∧ (1 + a) / P = a / P + 1) := by
  have ha := Nat.mod_add_div a P
  have hs := Nat.mod_lt a hP
  rcases Nat.lt_or_ge (a % P + 1) P with h | h
  · left
    have e : 1 + a = (a % P + 1) + P * (a / P) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt h,
      zero_add]
    exact ⟨h, rfl, rfl⟩
  · right
    have e : 1 + a = 0 + P * (a / P + 1) := by rw [Nat.mul_add]; omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hP]
    simp
    omega

private theorem mod_div_cases_of_sub_one (a P : ℕ) (hP : 0 < P) (ha : 1 ≤ a) :
    ((a - 1) % P + 1 < P ∧ a % P = (a - 1) % P + 1 ∧ a / P = (a - 1) / P) ∨
    ((a - 1) % P + 1 = P ∧ a % P = 0 ∧ a / P = (a - 1) / P + 1) := by
  have := one_add_mod_div_cases (a - 1) P hP
  rwa [Nat.add_sub_cancel' ha] at this

theorem Fdig_der_inl (j0 : ZMod J) (l : Fin (Dt.nL j0)) (a0 : Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inl l⟩, a0) H) = pderiv (Dt.liftVar (⟨j0, Sum.inl l⟩, a0)) (Dt.Fdig rho H) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w
          = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    by_cases hd : Dt.digOK rho mo
    · rw [if_pos ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).2 hd), if_pos hd, pderiv_monomial,
        liftMon_apply_liftVar, Pof_inl, Nat.div_one]
      rcases Nat.eq_zero_or_pos (mo (⟨j0, Sum.inl l⟩, a0)) with h0 | h0
      · simp [h0]
      · congr 1
        have e2 := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inl l⟩, a0) : TL J Dt.nL r × Fin r) 1) mo
          (⟨j0, Sum.inl l⟩, a0) 1 (fun w hw => (e1 w hw).symm)
          (by simp only [Pof_inl, Nat.div_one, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega)
        rw [e2, add_tsub_cancel_right]
    · rw [if_neg (fun h => hd ((digOK_iff_of_eq_off_inl Dt j0 l a0 rho mo _ e1).1 h)), if_neg hd, map_zero]
  · rw [map_add, Fdig_add, Fdig_add, hp, hq, map_add]

section Tau

variable (j0 : ZMod J) (m0 a0 : Fin r) (hP : 0 < Dt.P j0 m0) (rho : (ZMod J × Fin r) × Fin r → ℕ)

include hP

theorem Fdig_big (h : Dt.P j0 m0 ≤ rho ((j0, m0), a0)) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho H = 0 := by
  unfold SignedChainData.Fdig
  apply Finset.sum_eq_zero
  intro mo hmo
  have h3 := (Finset.mem_filter.1 hmo).2 j0 m0 a0
  have h4 := Nat.mod_lt (mo (⟨j0, Sum.inr m0⟩, a0)) hP
  omega

theorem Fdig_mul_zero (h : rho ((j0, m0), a0) = 0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inr m0⟩, a0) * H) =
      X (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0)) * Dt.Fdig (Function.update rho ((j0, m0), a0) (Dt.P j0 m0 - 1)) H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) := by simp
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    rcases one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hn : ¬ Dt.digOK rho (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo) := by
        intro hd
        have := hd j0 m0 a0
        rw [hv1, h2, h] at this
        omega
      have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by
        rw [hv1, h2, h]
        constructor <;> intro <;> omega)
      rw [if_neg hn, if_neg (fun h' => hn (hd.2 h')), mul_zero]
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (Dt.P j0 m0 - 1) mo _ e1 (by
        rw [hv1, h2, h]
        constructor <;> intro <;> omega)
      by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (Dt.P j0 m0 - 1)) mo
      · rw [if_pos (hd.2 hd'), if_pos hd', X_mul_monomialPlaneCoefficients,
          liftMon_eq_add_single_of_eq_off Dt mo _ _ 1 e1 (by rw [hv1, Pof_inr, h3]), add_comm]
      · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd', mul_zero]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq, mul_add]

theorem Fdig_mul_pos (h1 : 0 < rho ((j0, m0), a0)) (h2 : rho ((j0, m0), a0) < Dt.P j0 m0)
    (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (X (⟨j0, Sum.inr m0⟩, a0) * H) =
      Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) H := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 + mo : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = 1 + mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) := by simp
    rw [X_mul_monomialPlaneCoefficients, Fdig_mono, Fdig_mono]
    rcases one_add_mod_div_cases (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by
        rw [hv1, k2]
        constructor <;> intro <;> omega)
      by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo
      · rw [if_pos (hd.2 hd'), if_pos hd',
          liftMon_eq_add_single_of_eq_off Dt mo _ _ 0 e1 (by rw [hv1, Pof_inr, k3, add_zero]), Finsupp.single_zero, add_zero]
      · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
    · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) - 1) mo _ e1 (by
        rw [hv1, k2]
        constructor <;> intro <;> omega)
      have hn : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) - 1)) mo := by
        intro hd'
        have := hd' j0 m0 a0
        rw [Function.update_self] at this
        omega
      rw [if_neg (fun h' => hn (hd.1 h')), if_neg hn]
  · rw [mul_add, Fdig_add, Fdig_add, hp, hq]

theorem Fdig_der_lt (h : rho ((j0, m0), a0) + 1 < Dt.P j0 m0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inr m0⟩, a0) H) =
      ((rho ((j0, m0), a0) + 1 : ℕ) : KK O) • Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) H +
      ((Dt.P j0 m0 : ℕ) : KK O) • (X (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0)) * pderiv (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0))
        (Dt.Fdig (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) H)) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1 := by simp
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha
    · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo := by
        intro hd
        have := hd j0 m0 a0
        rw [Function.update_self, ha, Nat.zero_mod] at this
        omega
      rw [if_neg hn', ha]
      simp
    · rcases mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho (rho ((j0, m0), a0) + 1) mo _ e1 (by
          rw [hv1, k2]
          constructor <;> intro <;> omega)
        by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo
        · have hk : mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) % Dt.P j0 m0 = rho ((j0, m0), a0) + 1 := by
            have := hd' j0 m0 a0
            rwa [Function.update_self] at this
          have hL := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 0 (fun w hw => (e1 w hw).symm)
            (by rw [hv1, Pof_inr, k3, add_zero])
          rw [Finsupp.single_zero, add_zero] at hL
          rw [if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ← hL, X_mul_monomialPlaneCoefficients]
          have hc : ((rho ((j0, m0), a0) + 1 : ℕ) : KK O) + ((Dt.P j0 m0 : ℕ) : KK O) *
              ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O) := by
            rw [← Nat.cast_mul, ← Nat.cast_add, ← hk, Nat.mod_add_div]
          rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0) with hq | hq
          · rw [hq] at hc ⊢
            simp only [Nat.cast_zero, mul_zero, map_zero, smul_zero, add_zero, smul_monomial] at hc ⊢
            rw [smul_eq_mul, ← hc, mul_comm]
          · have hLv : liftMon Dt mo (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 := by rw [liftMon_apply_liftVar, Pof_inr]
            have hs : Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1 + (liftMon Dt mo - Finsupp.single (Dt.liftVar ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) 1) = liftMon Dt mo := by
              ext w
              simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
              split_ifs with hw
              · subst hw
                omega
              · simp
            rw [hs, smul_monomial, smul_monomial, ← map_add, smul_eq_mul, smul_eq_mul, ← hc]
            congr 1
            ring
        · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
          simp
      · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) (rho ((j0, m0), a0) + 1)) mo := by
          intro hd
          have := hd j0 m0 a0
          rw [Function.update_self, k2] at this
          omega
        have hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) := by
          intro hd
          have := hd j0 m0 a0
          rw [hv1] at this
          omega
        rw [if_neg hn, if_neg hn']
        simp
  · simp only [map_add, Fdig_add, hp, hq, smul_add, mul_add]
    abel

theorem Fdig_der_eq (h : rho ((j0, m0), a0) + 1 = Dt.P j0 m0) (H : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (pderiv (⟨j0, Sum.inr m0⟩, a0) H) =
      ((Dt.P j0 m0 : ℕ) : KK O) • pderiv (Dt.liftVar (⟨j0, Sum.inr m0⟩, a0))
        (Dt.Fdig (Function.update rho ((j0, m0), a0) 0) H) := by
  refine MvPolynomial.induction_on' H (fun mo c => ?_) (fun p q hp hq => ?_)
  · have e1 : ∀ w : TL J Dt.nL r × Fin r, w ≠ ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) →
        (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) w = mo w := by
      intro w hw
      simp [Finsupp.single_apply, Ne.symm hw]
    have hv1 : (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 : TL J Dt.nL r × Fin r →₀ ℕ) ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) = mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) - 1 := by simp
    rw [pderiv_monomial, Fdig_mono, Fdig_mono]
    rcases Nat.eq_zero_or_pos (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) with ha | ha
    · by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo
      · rw [if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, ha]
        simp
      · rw [if_neg hd', ha]
        simp
    · rcases mod_div_cases_of_sub_one (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0) hP ha with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
      · have hn' : ¬ Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo := by
          intro hd
          have := hd j0 m0 a0
          rw [Function.update_self, k2] at this
          omega
        have hn : ¬ Dt.digOK rho (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) := by
          intro hd
          have := hd j0 m0 a0
          rw [hv1] at this
          omega
        rw [if_neg hn, if_neg hn']
        simp
      · have hd := digOK_iff_update_of_eq_off_inr Dt j0 m0 a0 rho 0 mo _ e1 (by
          rw [hv1, k2]
          constructor <;> intro <;> omega)
        by_cases hd' : Dt.digOK (Function.update rho ((j0, m0), a0) 0) mo
        · have hL := liftMon_eq_add_single_of_eq_off Dt (mo - Finsupp.single ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1) mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) 1 (fun w hw => (e1 w hw).symm)
            (by rw [hv1, Pof_inr, k3])
          have hc : ((Dt.P j0 m0 : ℕ) : KK O) * ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) / Dt.P j0 m0 : ℕ) : KK O) = ((mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r) : ℕ) : KK O) := by
            rw [← Nat.cast_mul]
            congr 1
            have := Nat.mod_add_div (mo ((⟨j0, Sum.inr m0⟩, a0) : TL J Dt.nL r × Fin r)) (Dt.P j0 m0)
            rw [k2, zero_add] at this
            exact this
          rw [if_pos (hd.2 hd'), if_pos hd', pderiv_monomial, liftMon_apply_liftVar, Pof_inr, hL, add_tsub_cancel_right,
            smul_monomial, smul_eq_mul, ← hc]
          congr 1
          ring
        · rw [if_neg (fun h' => hd' (hd.1 h')), if_neg hd']
          simp
  · simp only [map_add, Fdig_add, hp, hq, smul_add]

end Tau

theorem Fdig_der_ex (hP : ∀ j m, 0 < Dt.P j m) (v0 : TL J Dt.nL r × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) :
    ∃ (c1 c2 c3 : KK O) (rho1 rho2 : (ZMod J × Fin r) × Fin r → ℕ), (c2 ≠ 0 → Dt.trueLet.vec v0.1 = true) ∧
      ∀ H, Dt.Fdig rho (pderiv v0 H) = c1 • Dt.Fdig rho1 H +
        c2 • (X (Dt.liftVar v0) * pderiv (Dt.liftVar v0) (Dt.Fdig rho1 H)) +
        c3 • pderiv (Dt.liftVar v0) (Dt.Fdig rho2 H) := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩
  · refine ⟨0, 0, 1, rho, rho, fun h => absurd rfl h, fun H => ?_⟩
    rw [Fdig_der_inl]
    simp
  · have hPm := hP j m
    rcases lt_trichotomy (rho ((j, m), a) + 1) (Dt.P j m) with h | h | h
    · refine ⟨((rho ((j, m), a) + 1 : ℕ) : KK O), ((Dt.P j m : ℕ) : KK O), 0,
        Function.update rho ((j, m), a) (rho ((j, m), a) + 1), rho, fun _ => rfl, fun H => ?_⟩
      rw [Fdig_der_lt Dt j m a hPm rho h H]
      simp
    · refine ⟨0, 0, ((Dt.P j m : ℕ) : KK O), rho, Function.update rho ((j, m), a) 0,
        fun h => absurd rfl h, fun H => ?_⟩
      rw [Fdig_der_eq Dt j m a hPm rho h H]
      simp
    · refine ⟨0, 0, 0, rho, rho, fun h => absurd rfl h, fun H => ?_⟩
      rw [Fdig_big Dt j m a hPm rho (by omega)]
      simp

theorem Fdig_mul_ex (hP : ∀ j m, 0 < Dt.P j m) (v0 : TL J Dt.nL r × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) :
    ∃ (c1 c2 : KK O) (rho1 rho2 : (ZMod J × Fin r) × Fin r → ℕ),
      ∀ H, Dt.Fdig rho (X v0 * H) = c1 • Dt.Fdig rho1 H + c2 • (X (Dt.liftVar v0) * Dt.Fdig rho2 H) := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩
  · refine ⟨0, 1, rho, rho, fun H => ?_⟩
    rw [Fdig_mul_inl]
    simp
  · have hPm := hP j m
    by_cases h0 : rho ((j, m), a) = 0
    · refine ⟨0, 1, rho, Function.update rho ((j, m), a) (Dt.P j m - 1), fun H => ?_⟩
      rw [Fdig_mul_zero Dt j m a hPm rho h0 H]
      simp
    · by_cases h1 : rho ((j, m), a) < Dt.P j m
      · refine ⟨1, 0, Function.update rho ((j, m), a) (rho ((j, m), a) - 1), rho, fun H => ?_⟩
        rw [Fdig_mul_pos Dt j m a hPm rho (Nat.pos_of_ne_zero h0) h1 H]
        simp
      · refine ⟨0, 0, rho, rho, fun H => ?_⟩
        rw [Fdig_big Dt j m a hPm rho (by omega)]
        simp

theorem modelLet_vec (v0 : TL J Dt.nL r × Fin r) : Dt.modelLet.vec (Dt.liftVar v0).1 = Dt.trueLet.vec v0.1 := by
  rcases v0 with ⟨⟨j, l | m⟩, a⟩ <;> rfl

end Formalism.MainNotions.PairMembershipBlocks
