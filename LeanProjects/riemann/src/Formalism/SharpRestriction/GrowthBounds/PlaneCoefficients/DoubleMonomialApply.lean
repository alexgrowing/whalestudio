import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks.Tr

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Gen

variable {σ R : Type*} [CommSemiring R]

theorem X_mul_mon (i : σ) (s : σ →₀ ℕ) (q : R) : X i * monomial s q = monomial (s + Finsupp.single i 1) q := by
  rw [show (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 from rfl, monomial_mul, one_mul, add_comm]

theorem pderiv_mon_succ (i : σ) (s : σ →₀ ℕ) (q : R) :
    pderiv i (monomial (s + Finsupp.single i 1) q) = monomial s ((s i + 1) • q) := by
  rw [pderiv_monomial, add_tsub_cancel_right, nsmul_eq_mul, mul_comm, Finsupp.add_apply, Finsupp.single_eq_same]

theorem pderiv_mon_zero (i : σ) (s : σ →₀ ℕ) (q : R) (h : s i = 0) : pderiv i (monomial s q) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (i : σ) (s : σ →₀ ℕ) (h : s i ≠ 0) : ∃ s', s = s' + Finsupp.single i 1 :=
  ⟨s - Finsupp.single i 1,
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h))).symm⟩

theorem euler_mon (i : σ) (s : σ →₀ ℕ) (q : R) : X i * pderiv i (monomial s q) = monomial s (s i • q) := by
  by_cases h : s i = 0
  · rw [pderiv_mon_zero i s q h, mul_zero, h, zero_smul, map_zero]
  · obtain ⟨s', rfl⟩ := exists_add_single i s h
    rw [pderiv_mon_succ, X_mul_mon, Finsupp.add_apply, Finsupp.single_eq_same]

end Gen

theorem oneT_monomial {σ τ Kf : Type} [Field Kf] (e : Module.End Kf (MvPolynomial τ Kf)) (s : σ →₀ ℕ)
    (q : MvPolynomial τ Kf) : oneT e (monomial s q) = monomial s (e q) := by
  unfold oneT
  by_cases h : q = 0
  · subst h; simp
  · rw [support_monomial, if_neg h, Finset.sum_singleton, coeff_monomial, if_pos rfl]

theorem nat_A {P e t : ℕ} (h : t + 1 < P) : e % P = t ↔ (e + 1) % P = t + 1 := by
  constructor
  · intro he
    have h1 := Nat.div_add_mod e P
    have h2 : e + 1 = P * (e / P) + (t + 1) := by omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro he
    have h1 := Nat.div_add_mod (e + 1) P
    have h2 : e = P * ((e + 1) / P) + t := by omega
    calc e % P = (P * ((e + 1) / P) + t) % P := by rw [← h2]
      _ = t := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem nat_A_div {P e t : ℕ} (h : t + 1 < P) (he : e % P = t) : (e + 1) / P = e / P := by
  have h1 := Nat.div_add_mod e P
  have h2 : e + 1 = P * (e / P) + (t + 1) := by omega
  calc (e + 1) / P = (P * (e / P) + (t + 1)) / P := by rw [← h2]
    _ = e / P := by rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt h, add_zero]

theorem nat_B_eq {P e t : ℕ} (h : t + 1 = P) (he : e % P = t) : e + 1 = P * (e / P + 1) := by
  have h1 := Nat.div_add_mod e P
  rw [mul_add, mul_one]
  omega

theorem nat_B {P e t : ℕ} (h : t + 1 = P) : e % P = t ↔ (e + 1) % P = 0 := by
  constructor
  · intro he
    rw [nat_B_eq h he, Nat.mul_mod_right]
  · intro he
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [mul_add, mul_one] at hk
      have h2 : e = P * k + t := by omega
      rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

theorem nat_B_div {P e t : ℕ} (h : t + 1 = P) (he : e % P = t) : (e + 1) / P = e / P + 1 := by
  rw [nat_B_eq h he, Nat.mul_div_cancel_left _ (by omega)]

section Core

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def aVar (x : TL J nL r) (c : Fin (r + K)) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm c)

theorem plVar_eq (x : TL J nL r) (a : Fin r) : plVar Fr hk nL x a = aVar Fr hk nL x (Fin.castAdd K a) := rfl

theorem noVar_eq (x : TL J nL r) (b : Fin K) : noVar Fr hk nL x b = aVar Fr hk nL x (Fin.natAdd r b) := rfl

theorem inLow_iff (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InLow Fr p hk nL rho mo ↔ ∀ x c, mo (aVar Fr hk nL x c) % lowP Fr p x = rho (x, c) := by
  constructor
  · intro h x c
    exact Fin.addCases (motive := fun c => mo (aVar Fr hk nL x c) % lowP Fr p x = rho (x, c))
      (fun a => h.1 x a) (fun b => h.2 x b) c
  · intro h
    exact ⟨fun x a => h x _, fun x b => h x _⟩

theorem plMon_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    plMon Fr p hk nL mo (x, a) = mo (aVar Fr hk nL x (Fin.castAdd K a)) / lowP Fr p x := by
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm]
  rfl

theorem noMon_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    noMon Fr p hk nL mo (x, b) = mo (aVar Fr hk nL x (Fin.natAdd r b)) / lowP Fr p x := by
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rfl

theorem inBlock_iff (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) :
    InBlock Fr p hk nL dPl dNo mo ↔
      (∀ x, ∑ a : Fin r, plMon Fr p hk nL mo (x, a) = dPl x) ∧ ∀ x, ∑ b : Fin K, noMon Fr p hk nL mo (x, b) = dNo x := by
  simp only [plMon_apply, noMon_apply]
  rfl

variable {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)
  (c0 : Fin (r + K))

include hx0 in
theorem aVar_inj {x : TL J nL r} {c c0 : Fin (r + K)} (h : aVar Fr hk nL x c = aVar Fr hk nL x0 c0) :
    (x, c) = (x0, c0) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [aVar] at h1 h2
  rw [hx0 x h1, Fin.cast_injective _ h2]

include hx0 in
theorem step_apply (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) =
      mo (aVar Fr hk nL x c) + if (x, c) = (x0, c0) then 1 else 0 := by
  rw [Finsupp.add_apply, Finsupp.single_apply]
  congr 1
  by_cases h : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [if_pos h, if_pos (by rw [h1, h2])]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (aVar_inj Fr hk nL hx0 h'.symm)

include hx0 in
theorem inLow_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) :
    InLow Fr p hk nL rho mo ↔ InLow Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1))
      (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) := by
  rw [inLow_iff, inLow_iff]
  refine forall_congr' fun x => forall_congr' fun c => ?_
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl, Function.update_self]
    exact nat_A h
  · rw [if_neg hv, Function.update_of_ne hv, add_zero]

include hx0 in
theorem inLow_B (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 = lowP Fr p x0) :
    InLow Fr p hk nL rho mo ↔ InLow Fr p hk nL (Function.update rho (x0, c0) 0)
      (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) := by
  rw [inLow_iff, inLow_iff]
  refine forall_congr' fun x => forall_congr' fun c => ?_
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl, Function.update_self]
    exact nat_B h
  · rw [if_neg hv, Function.update_of_ne hv, add_zero]

include hx0 in
theorem div_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) / lowP Fr p x =
      mo (aVar Fr hk nL x c) / lowP Fr p x := by
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl]
    exact nat_A_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)
  · rw [if_neg hv, add_zero]

include hx0 in
theorem div_B (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) (x : TL J nL r) (c : Fin (r + K)) :
    (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1 : TV n' (m + 1) →₀ ℕ) (aVar Fr hk nL x c) / lowP Fr p x =
      mo (aVar Fr hk nL x c) / lowP Fr p x + if (x, c) = (x0, c0) then 1 else 0 := by
  rw [step_apply Fr hk nL hx0]
  by_cases hv : (x, c) = (x0, c0)
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [h1, h2, if_pos rfl]
    exact nat_B_div h ((inLow_iff Fr p hk nL rho mo).1 hL x0 c0)
  · rw [if_neg hv, add_zero, add_zero]

include hx0 in
theorem plMon_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) = plMon Fr p hk nL mo := by
  ext ⟨x, a⟩
  rw [plMon_apply, plMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]

include hx0 in
theorem noMon_A (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) = noMon Fr p hk nL mo := by
  ext ⟨x, b⟩
  rw [noMon_apply, noMon_apply, div_A Fr p hk nL hx0 c0 rho mo h hL]

theorem cast_ne_nat (a : Fin r) (b : Fin K) : Fin.natAdd r b ≠ Fin.castAdd K a := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
  have := a.isLt
  omega

include hx0 in
theorem plMon_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) =
      plMon Fr p hk nL mo + Finsupp.single (x0, a) 1 := by
  ext ⟨x, a'⟩
  rw [plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, plMon_apply, Finsupp.single_apply]
  congr 1
  by_cases hv : (x0, a) = (x, a')
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [if_pos hv, if_pos (by rw [h1, h2])]
  · rw [if_neg hv, if_neg]
    intro h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact hv (by rw [h1, Fin.castAdd_injective r K h2])

include hx0 in
theorem noMon_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) = noMon Fr p hk nL mo := by
  ext ⟨x, b⟩
  rw [noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, noMon_apply, if_neg, add_zero]
  intro h'
  exact cast_ne_nat a b (Prod.mk.inj h').2

include hx0 in
theorem noMon_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    noMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) =
      noMon Fr p hk nL mo + Finsupp.single (x0, b) 1 := by
  ext ⟨x, b'⟩
  rw [noMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, Finsupp.add_apply, noMon_apply, Finsupp.single_apply]
  congr 1
  by_cases hv : (x0, b) = (x, b')
  · obtain ⟨h1, h2⟩ := Prod.mk.inj hv
    rw [if_pos hv, if_pos (by rw [h1, h2])]
  · rw [if_neg hv, if_neg]
    intro h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact hv (by rw [h1, Fin.natAdd_injective K r h2])

include hx0 in
theorem plMon_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (hL : InLow Fr p hk nL rho mo) :
    plMon Fr p hk nL (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) = plMon Fr p hk nL mo := by
  ext ⟨x, a⟩
  rw [plMon_apply, div_B Fr p hk nL hx0 _ rho mo h hL, plMon_apply, if_neg, add_zero]
  intro h'
  exact cast_ne_nat a b (Prod.mk.inj h').2.symm

theorem sum_add_single {ι : Type} [DecidableEq ι] {n : ℕ} (f : ι × Fin n →₀ ℕ) (x0 x : ι) (a : Fin n) :
    ∑ a' : Fin n, (f + Finsupp.single (x0, a) 1 : ι × Fin n →₀ ℕ) (x, a') = ∑ a' : Fin n, f (x, a') + if x = x0 then 1 else 0 := by
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : x = x0
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [Finsupp.single_eq_same]
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro h'
      exact hb (Prod.mk.inj h').2.symm
    · intro h'
      exact absurd (Finset.mem_univ a) h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (Prod.mk.inj h').1.symm

theorem deg_upd {ι : Type} [DecidableEq ι] (S d : ι → ℕ) (x0 : ι) :
    (∀ x, S x = d x) ↔ ∀ x, (S x + if x = x0 then 1 else 0) = Function.update d x0 (d x0 + 1) x := by
  refine forall_congr' fun x => ?_
  by_cases h : x = x0
  · subst h
    rw [if_pos rfl, Function.update_self]
    omega
  · rw [if_neg h, Function.update_of_ne h, add_zero]

end Core

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem levImg_monomial (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (c : KK O) :
    levImg Fr p hk nL rho dPl dNo (monomial mo c) =
      if InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo then
        mono2 (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) c else 0 := by
  unfold levImg
  by_cases h : c = 0
  · subst h
    simp
  · rw [support_monomial, if_neg h, Finset.filter_singleton]
    by_cases h1 : InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos h1, if_pos h1, Finset.sum_singleton, coeff_monomial, if_pos rfl]
      rfl
    · rw [if_neg h1, if_neg h1, Finset.sum_empty]

theorem levImg_empty (hp : 0 < p) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (x0 : TL J nL r)
    (c0 : Fin (r + K)) (h : lowP Fr p x0 ≤ rho (x0, c0)) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo F = 0 := by
  unfold levImg
  apply Finset.sum_eq_zero
  intro mo hmo
  exfalso
  have h1 := (inLow_iff Fr p hk nL rho mo).1 (Finset.mem_filter.1 hmo).2.1 x0 c0
  have h2 := Nat.mod_lt (mo (aVar Fr hk nL x0 c0)) (pow_pos hp (Fr.dist (segZ x0.1) (posTL Fr x0)))
  unfold lowP at h h1
  omega

theorem double_monomial_apply {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) :
    mono2 a b c = monomial a (monomial b c) := rfl

theorem pl_euler {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    X i * pderiv i (mono2 a b c) = mono2 a b ((a i : Kf) * c) := by
  rw [double_monomial_apply, euler_mon, smul_monomial, nsmul_eq_mul, double_monomial_apply]

theorem pl_der {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    pderiv i (mono2 (a + Finsupp.single i 1) b c) = mono2 a b (((a i + 1 : ℕ) : Kf) * c) := by
  rw [double_monomial_apply, pderiv_mon_succ, smul_monomial, nsmul_eq_mul, double_monomial_apply]

theorem pl_der_zero {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) (h : a i = 0) :
    pderiv i (mono2 a b c) = 0 := by
  rw [double_monomial_apply, pderiv_mon_zero _ _ _ h]

theorem pl_mul {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : σ) :
    X i * mono2 a b c = mono2 (a + Finsupp.single i 1) b c := by
  rw [double_monomial_apply, X_mul_mon, double_monomial_apply]

theorem no_euler {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (mulN i * derN i) (mono2 a b c) = mono2 a b ((b i : Kf) * c) := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show X i * pderiv i (monomial b c) = _
  rw [euler_mon, nsmul_eq_mul]

theorem no_der {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (derN i) (mono2 a (b + Finsupp.single i 1) c) = mono2 a b (((b i + 1 : ℕ) : Kf) * c) := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show pderiv i (monomial (b + Finsupp.single i 1) c) = _
  rw [pderiv_mon_succ, nsmul_eq_mul]

theorem no_der_zero {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) (h : b i = 0) :
    oneT (derN i) (mono2 a b c) = 0 := by
  rw [double_monomial_apply, oneT_monomial]
  have : derN i (monomial b c) = 0 := pderiv_mon_zero i b c h
  rw [this, map_zero]

theorem no_mul {σ τ Kf : Type} [Field Kf] (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c : Kf) (i : τ) :
    oneT (mulN i) (mono2 a b c) = mono2 a (b + Finsupp.single i 1) c := by
  rw [double_monomial_apply, oneT_monomial, double_monomial_apply]
  congr 1
  show X i * monomial b c = _
  rw [X_mul_mon]

end Lev

section Main

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
  {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)

include hx0 in
theorem lev_A (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) dPl dNo
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) c) =
      levImg Fr p hk nL rho dPl dNo (monomial mo c) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_A Fr p hk nL hx0 c0 rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hpl := plMon_A Fr p hk nL hx0 c0 rho mo h hL
    have hno := noMon_A Fr p hk nL hx0 c0 rho mo h hL
    have hB : InBlock Fr p hk nL dPl dNo (mo + Finsupp.single (aVar Fr hk nL x0 c0) 1) ↔
        InBlock Fr p hk nL dPl dNo mo := by
      rw [inBlock_iff, inBlock_iff, hpl, hno]
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, hpl, hno]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2)]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1)]

include hx0 in
theorem block_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (hL : InLow Fr p hk nL rho mo) :
    InBlock Fr p hk nL (Function.update dPl x0 (dPl x0 + 1)) dNo
        (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) ↔ InBlock Fr p hk nL dPl dNo mo := by
  rw [inBlock_iff, inBlock_iff, plMon_Bpl Fr p hk nL hx0 a rho mo h hL, noMon_Bpl Fr p hk nL hx0 a rho mo h hL]
  simp only [sum_add_single]
  exact and_congr (deg_upd (fun x => ∑ a' : Fin r, plMon Fr p hk nL mo (x, a')) dPl x0).symm Iff.rfl

include hx0 in
theorem block_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (hL : InLow Fr p hk nL rho mo) :
    InBlock Fr p hk nL dPl (Function.update dNo x0 (dNo x0 + 1))
        (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) ↔ InBlock Fr p hk nL dPl dNo mo := by
  rw [inBlock_iff, inBlock_iff, plMon_Bno Fr p hk nL hx0 b rho mo h hL, noMon_Bno Fr p hk nL hx0 b rho mo h hL]
  simp only [sum_add_single]
  exact and_congr Iff.rfl (deg_upd (fun x => ∑ b' : Fin K, noMon Fr p hk nL mo (x, b')) dNo x0).symm

include hx0 in
theorem lev_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.castAdd K a)) 1) c) =
      X (x0, a) * levImg Fr p hk nL rho dPl dNo (monomial mo c) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_B Fr p hk nL hx0 (Fin.castAdd K a) rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hB := block_Bpl Fr p hk nL hx0 a rho dPl dNo h mo hL
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bpl Fr p hk nL hx0 a rho mo h hL,
        noMon_Bpl Fr p hk nL hx0 a rho mo h hL, pl_mul]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), mul_zero]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), mul_zero]

include hx0 in
theorem lev_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1))
        (monomial (mo + Finsupp.single (aVar Fr hk nL x0 (Fin.natAdd r b)) 1) c) =
      oneT (mulN (x0, b)) (levImg Fr p hk nL rho dPl dNo (monomial mo c)) := by
  rw [levImg_monomial, levImg_monomial]
  have hiff := inLow_B Fr p hk nL hx0 (Fin.natAdd r b) rho mo h
  by_cases hL : InLow Fr p hk nL rho mo
  · have hB := block_Bno Fr p hk nL hx0 b rho dPl dNo h mo hL
    by_cases hBl : InBlock Fr p hk nL dPl dNo mo
    · rw [if_pos ⟨hiff.1 hL, hB.2 hBl⟩, if_pos ⟨hL, hBl⟩, plMon_Bno Fr p hk nL hx0 b rho mo h hL,
        noMon_Bno Fr p hk nL hx0 b rho mo h hL, no_mul]
    · rw [if_neg (fun hh => hBl (hB.1 hh.2)), if_neg (fun hh => hBl hh.2), oneT_zero]
  · rw [if_neg (fun hh => hL (hiff.2 hh.1)), if_neg (fun hh => hL hh.1), oneT_zero]

include hx0 in
theorem mul_A (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, c0) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) dPl dNo (X (aVar Fr hk nL x0 c0) * F) =
      levImg Fr p hk nL rho dPl dNo F := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_A Fr p hk nL hx0 c0 rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG]

include hx0 in
theorem mul_Bpl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo
        (X (aVar Fr hk nL x0 (Fin.castAdd K a)) * F) = X (x0, a) * levImg Fr p hk nL rho dPl dNo F := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_Bpl Fr p hk nL hx0 a rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, mul_add]

include hx0 in
theorem mul_Bno (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1))
        (X (aVar Fr hk nL x0 (Fin.natAdd r b)) * F) = oneT (mulN (x0, b)) (levImg Fr p hk nL rho dPl dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c => rw [X_mul_mon, lev_Bno Fr p hk nL hx0 b rho dPl dNo h]
  | add F G hF hG => rw [mul_add, levImg_add, levImg_add, hF, hG, oneT_add]

theorem upd_back {α : Type} [DecidableEq α] (f : α → ℕ) (v : α) (t : ℕ) : Function.update (Function.update f v t) v (f v) = f := by
  rw [Function.update_idem, Function.update_eq_self]

include hx0 in
theorem mul_Bpl_zero (hp : 0 < p) (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) = 0) (hd : dPl x0 = 0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (X (aVar Fr hk nL x0 (Fin.castAdd K a)) * F) = 0 := by
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    rw [X_mul_mon, levImg_monomial, if_neg]
    rintro ⟨hL, hB⟩
    have hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0 := by
      rw [Function.update_self]; omega
    have hiff := inLow_B Fr p hk nL hx0 (Fin.castAdd K a)
      (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) mo hs
    rw [← h, upd_back] at hiff
    have hL' := hiff.2 hL
    rw [inBlock_iff, plMon_Bpl Fr p hk nL hx0 a _ mo hs hL'] at hB
    have h1 := hB.1 x0
    rw [sum_add_single, if_pos rfl, hd] at h1
    omega
  | add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]

include hx0 in
theorem mul_Bno_zero (hp : 0 < p) (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) = 0) (hd : dNo x0 = 0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (X (aVar Fr hk nL x0 (Fin.natAdd r b)) * F) = 0 := by
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    rw [X_mul_mon, levImg_monomial, if_neg]
    rintro ⟨hL, hB⟩
    have hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0 := by
      rw [Function.update_self]; omega
    have hiff := inLow_B Fr p hk nL hx0 (Fin.natAdd r b)
      (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) mo hs
    rw [← h, upd_back] at hiff
    have hL' := hiff.2 hL
    rw [inBlock_iff, noMon_Bno Fr p hk nL hx0 b _ mo hs hL'] at hB
    have h1 := hB.2 x0
    rw [sum_add_single, if_pos rfl, hd] at h1
    omega
  | add F G hF hG => rw [mul_add, levImg_add, hF, hG, add_zero]

end Main

section Der

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
  {x0 : TL J nL r} (hx0 : ∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0)

theorem notLow_of_zero (c0 : Fin (r + K)) (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ)
    (h0 : mo (aVar Fr hk nL x0 c0) = 0) :
    ¬ InLow Fr p hk nL (Function.update rho (x0, c0) (rho (x0, c0) + 1)) mo := by
  intro hL
  have h1 := (inLow_iff Fr p hk nL _ mo).1 hL x0 c0
  rw [Function.update_self, h0, Nat.zero_mod] at h1
  omega

include hx0 in
theorem der_A_pl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.castAdd K a)) F) =
      ((rho (x0, Fin.castAdd K a) + 1 : ℕ) : KK O) •
        levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1)) dPl dNo F +
      ((lowP Fr p x0 : ℕ) : KK O) • (X (x0, a) * pderiv (x0, a)
        (levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1)) dPl dNo F)) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial,
        if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1)]
      simp
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, pl_euler, ← map_smul, ← map_smul, ← map_add]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 =
            (rho (x0, Fin.castAdd K a) + 1) + lowP Fr p x0 * plMon Fr p hk nL mo' (x0, a) := by
          rw [plMon_apply]
          have h1 := Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.castAdd K a))) (lowP Fr p x0)
          have h2 := (inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a)
          omega
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, mul_add, smul_add, hF, hG]
    abel

include hx0 in
theorem der_A_no (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 < lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.natAdd r b)) F) =
      ((rho (x0, Fin.natAdd r b) + 1 : ℕ) : KK O) •
        levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1)) dPl dNo F +
      ((lowP Fr p x0 : ℕ) : KK O) • oneT (mulN (x0, b) * derN (x0, b))
        (levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1)) dPl dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial,
        if_neg (fun hh => notLow_of_zero Fr p hk nL _ rho mo h0 hh.1), oneT_zero]
      simp
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_A Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, no_euler, ← map_smul, ← map_smul, ← map_add]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 =
            (rho (x0, Fin.natAdd r b) + 1) + lowP Fr p x0 * noMon Fr p hk nL mo' (x0, b) := by
          rw [noMon_apply]
          have h1 := Nat.div_add_mod (mo' (aVar Fr hk nL x0 (Fin.natAdd r b))) (lowP Fr p x0)
          have h2 := (inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b)
          omega
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc, oneT_zero]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, oneT_add, smul_add, hF, hG]
    abel

include hx0 in
theorem der_B_pl (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.castAdd K a) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.castAdd K a)) F) =
      ((lowP Fr p x0 : ℕ) : KK O) • pderiv (x0, a)
        (levImg Fr p hk nL (Function.update rho (x0, Fin.castAdd K a) 0) (Function.update dPl x0 (dPl x0 + 1)) dNo F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.castAdd K a)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial]
      split_ifs
      · rw [pl_der_zero _ _ _ _ (by rw [plMon_apply, h0, Nat.zero_div]), smul_zero]
      · rw [map_zero, smul_zero]
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_Bpl Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, pl_mul, pl_der, ← map_smul]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.castAdd K a)) + 1 =
            lowP Fr p x0 * (plMon Fr p hk nL mo' (x0, a) + 1) := by
          rw [plMon_apply]
          exact nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.castAdd K a))
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc]
        simp
  | add F G hF hG =>
    simp only [map_add, levImg_add, smul_add, hF, hG]

include hx0 in
theorem der_B_no (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (h : rho (x0, Fin.natAdd r b) + 1 = lowP Fr p x0) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levImg Fr p hk nL rho dPl dNo (pderiv (aVar Fr hk nL x0 (Fin.natAdd r b)) F) =
      ((lowP Fr p x0 : ℕ) : KK O) • oneT (derN (x0, b))
        (levImg Fr p hk nL (Function.update rho (x0, Fin.natAdd r b) 0) dPl (Function.update dNo x0 (dNo x0 + 1)) F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial mo c =>
    by_cases h0 : mo (aVar Fr hk nL x0 (Fin.natAdd r b)) = 0
    · rw [pderiv_mon_zero _ _ _ h0, levImg_zero, levImg_monomial]
      split_ifs
      · rw [no_der_zero _ _ _ _ (by rw [noMon_apply, h0, Nat.zero_div]), smul_zero]
      · rw [oneT_zero, smul_zero]
    · obtain ⟨mo', rfl⟩ := exists_add_single _ mo h0
      rw [pderiv_mon_succ, lev_Bno Fr p hk nL hx0 _ rho dPl dNo h, nsmul_eq_mul, levImg_monomial, levImg_monomial]
      by_cases hc : InLow Fr p hk nL rho mo' ∧ InBlock Fr p hk nL dPl dNo mo'
      · rw [if_pos hc, if_pos hc, no_mul, no_der, ← map_smul]
        congr 1
        have e1 : mo' (aVar Fr hk nL x0 (Fin.natAdd r b)) + 1 =
            lowP Fr p x0 * (noMon Fr p hk nL mo' (x0, b) + 1) := by
          rw [noMon_apply]
          exact nat_B_eq h ((inLow_iff Fr p hk nL rho mo').1 hc.1 x0 (Fin.natAdd r b))
        rw [e1]
        simp only [smul_eq_mul]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc, oneT_zero, oneT_zero, smul_zero]
  | add F G hF hG =>
    simp only [map_add, levImg_add, oneT_add, smul_add, hF, hG]

end Der

theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trDerPl : TrDerPl := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [plVar_eq]
  rcases lt_trichotomy (rho (x0, Fin.castAdd K a) + 1) (lowP Fr p x0) with h | h | h
  · refine ⟨((rho (x0, Fin.castAdd K a) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0,
      Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) + 1), rho, ?_⟩
    rw [der_A_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, add_zero]
  · refine ⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.castAdd K a) 0, ?_⟩
    rw [der_B_pl Fr p hk nL hx0 a rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]
  · refine ⟨0, 0, 0, rho, rho, ?_⟩
    rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, zero_smul, add_zero,
      add_zero]

theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trMulPl : TrMulPl := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 a rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  rw [plVar_eq]
  by_cases h0 : rho (x0, Fin.castAdd K a) = 0
  · by_cases hd : dPl x0 = 0
    · refine ⟨0, 0, rho, rho, fun _ => rfl, ?_⟩
      rw [mul_Bpl_zero Fr p hk nL hx0 hp a rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]
    · refine ⟨0, 1, rho, Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1), fun h => absurd h hd, ?_⟩
      have hs : Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1) (x0, Fin.castAdd K a) + 1 = lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_Bpl Fr p hk nL hx0 a (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1))
        (Function.update dPl x0 (dPl x0 - 1)) dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)) (x0, Fin.castAdd K a) 0 = rho := by
        have := upd_back rho (x0, Fin.castAdd K a) (lowP Fr p x0 - 1)
        rwa [h0] at this
      have e2 : Function.update (Function.update dPl x0 (dPl x0 - 1)) x0
          (Function.update dPl x0 (dPl x0 - 1) x0 + 1) = dPl := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]
        exact upd_back dPl x0 _
      rw [e1, e2] at key
      rw [key, zero_smul, zero_add, one_smul]
  · by_cases hlt : rho (x0, Fin.castAdd K a) < lowP Fr p x0
    · refine ⟨1, 0, Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1), rho, fun _ => rfl, ?_⟩
      have hs : Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1 < lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_A Fr p hk nL hx0 (Fin.castAdd K a) (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) dPl dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1)) (x0, Fin.castAdd K a)
          (Function.update rho (x0, Fin.castAdd K a) (rho (x0, Fin.castAdd K a) - 1) (x0, Fin.castAdd K a) + 1) = rho := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
        exact upd_back rho (x0, Fin.castAdd K a) _
      rw [e1] at key
      rw [key, one_smul, zero_smul, add_zero]
    · refine ⟨0, 0, rho, rho, fun _ => rfl, ?_⟩
      rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.castAdd K a) (by omega), zero_smul, zero_smul, add_zero]

theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trDerNo : TrDerNo := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [noVar_eq]
  rcases lt_trichotomy (rho (x0, Fin.natAdd r b) + 1) (lowP Fr p x0) with h | h | h
  · refine ⟨((rho (x0, Fin.natAdd r b) + 1 : ℕ) : KK O), ((lowP Fr p x0 : ℕ) : KK O), 0,
      Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) + 1), rho, ?_⟩
    rw [der_A_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, add_zero]
  · refine ⟨0, 0, ((lowP Fr p x0 : ℕ) : KK O), rho, Function.update rho (x0, Fin.natAdd r b) 0, ?_⟩
    rw [der_B_no Fr p hk nL hx0 b rho dPl dNo h F, zero_smul, zero_smul, zero_add, zero_add]
  · refine ⟨0, 0, 0, rho, rho, ?_⟩
    rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, zero_smul, add_zero,
      add_zero]

theorem _root_.Formalism.MainNotions.PairMembershipBlocks.trMulNo : TrMulNo := by
  intro p _ n' r K m _ O _ _ hk Fr J _ nL x0 hx0 b rho dPl dNo F
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hP : 0 < lowP Fr p x0 := pow_pos hp _
  rw [noVar_eq]
  by_cases h0 : rho (x0, Fin.natAdd r b) = 0
  · by_cases hd : dNo x0 = 0
    · refine ⟨0, 0, rho, rho, ?_⟩
      rw [mul_Bno_zero Fr p hk nL hx0 hp b rho dPl dNo h0 hd F, zero_smul, zero_smul, add_zero]
    · refine ⟨0, 1, rho, Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1), ?_⟩
      have hs : Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1) (x0, Fin.natAdd r b) + 1 = lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_Bno Fr p hk nL hx0 b (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1))
        dPl (Function.update dNo x0 (dNo x0 - 1)) hs F
      have e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)) (x0, Fin.natAdd r b) 0 = rho := by
        have := upd_back rho (x0, Fin.natAdd r b) (lowP Fr p x0 - 1)
        rwa [h0] at this
      have e2 : Function.update (Function.update dNo x0 (dNo x0 - 1)) x0
          (Function.update dNo x0 (dNo x0 - 1) x0 + 1) = dNo := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hd)]
        exact upd_back dNo x0 _
      rw [e1, e2] at key
      rw [key, zero_smul, zero_add, one_smul]
  · by_cases hlt : rho (x0, Fin.natAdd r b) < lowP Fr p x0
    · refine ⟨1, 0, Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1), rho, ?_⟩
      have hs : Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1 < lowP Fr p x0 := by
        rw [Function.update_self]; omega
      have key := mul_A Fr p hk nL hx0 (Fin.natAdd r b) (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) dPl dNo hs F
      have e1 : Function.update (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1)) (x0, Fin.natAdd r b)
          (Function.update rho (x0, Fin.natAdd r b) (rho (x0, Fin.natAdd r b) - 1) (x0, Fin.natAdd r b) + 1) = rho := by
        rw [Function.update_self, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
        exact upd_back rho (x0, Fin.natAdd r b) _
      rw [e1] at key
      rw [key, one_smul, zero_smul, add_zero]
    · refine ⟨0, 0, rho, rho, ?_⟩
      rw [levImg_empty Fr p hk nL hp rho dPl dNo x0 (Fin.natAdd r b) (by omega), zero_smul, zero_smul, add_zero]

end Formalism.MainNotions.PairMembershipBlocks.Tr
