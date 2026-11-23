import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementB
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.InitPartZeroXMul

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem pow_mul_mem (v : σ) (e : ℕ) (Q : Set (σ →₀ ℕ)) (g : MvPolynomial σ ℚ_[p]) :
    X v ^ e * g ∈ restrictSupport ℚ_[p] Q ↔ g ∈ restrictSupport ℚ_[p] {m | Finsupp.single v e + m ∈ Q} := by
  classical
  have c1 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff m (X v ^ e * g') =
      if e ≤ m v then coeff (m - Finsupp.single v e) g' else 0 := by
    intro m g'
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  have c2 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff (m + Finsupp.single v e) (X v ^ e * g') = coeff m g' := by
    intro m g'
    rw [c1, if_pos (by simp), add_tsub_cancel_right]
  rw [mem_restrictSupport_iff, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    have h1 : coeff (m + Finsupp.single v e) (X v ^ e * g) ≠ 0 := by
      rwa [c2, ← mem_support_iff]
    have h2 := h (mem_support_iff.mpr h1)
    show Finsupp.single v e + m ∈ Q
    rwa [add_comm]
  · intro h m hm
    rw [Finset.mem_coe, mem_support_iff, c1] at hm
    split_ifs at hm with hle
    · have h2 : m - Finsupp.single v e ∈ {m | Finsupp.single v e + m ∈ Q} := h (mem_support_iff.mpr hm)
      simp only [Set.mem_setOf_eq] at h2
      rwa [add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hle)] at h2
    · exact absurd rfl hm

theorem pow_mul_int_iff (v : σ) (e : ℕ) (a : MvPolynomial σ ℚ_[p]) :
    X v ^ e * a ∈ IntPol p σ ↔ a ∈ IntPol p σ := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', mul_assoc, X_mul_int_iff, ih]

theorem pow_mul_order (v : σ) (e : ℕ) (h : MvPolynomial σ ℚ_[p]) :
    X v ^ e * h ∈ restrictSupport ℚ_[p] {m : σ →₀ ℕ | e ≤ m v} := by
  classical
  have c1 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff m (X v ^ e * g') =
      if e ≤ m v then coeff (m - Finsupp.single v e) g' else 0 := by
    intro m g'
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  rw [mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, mem_support_iff, c1] at hm
  split_ifs at hm with hle
  · exact hle
  · exact absurd rfl hm

theorem exists_pow_div (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p])
    (hf : f ∈ restrictSupport ℚ_[p] {m : σ →₀ ℕ | e ≤ m v}) : ∃ h, f = X v ^ e * h := by
  classical
  have hsupp := hf
  rw [mem_restrictSupport_iff] at hsupp
  refine ⟨MvPolynomial.divMonomial f (Finsupp.single v e), ?_⟩
  have hmod : MvPolynomial.modMonomial f (Finsupp.single v e) = 0 := by
    ext m
    rw [coeff_zero]
    by_cases hle : Finsupp.single v e ≤ m
    · rw [MvPolynomial.coeff_modMonomial_of_le _ hle]
    · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hle]
      by_contra hne
      exact hle (Finsupp.single_le_iff.mpr (hsupp (mem_support_iff.mpr hne)))
  have hdm := MvPolynomial.divMonomial_add_modMonomial f (Finsupp.single v e)
  rw [hmod, add_zero, ← X_pow_eq_monomial] at hdm
  exact hdm.symm

theorem initPart_pow_mul (v : σ) (e : ℕ) (h : MvPolynomial σ ℚ_[p]) :
    initPart v e (X v ^ e * h) = X v ^ e * initPart v 0 h := by
  classical
  have c1 : ∀ (m : σ →₀ ℕ) (g' : MvPolynomial σ ℚ_[p]), coeff m (X v ^ e * g') =
      if e ≤ m v then coeff (m - Finsupp.single v e) g' else 0 := by
    intro m g'
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    simp only [Finsupp.single_le_iff, one_mul]
  ext m
  rw [coeff_initPart, c1, c1, coeff_initPart]
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
  split_ifs <;> first | rfl | omega | (exfalso; omega)

theorem initPart_zero' (v : σ) (e : ℕ) : initPart v e (0 : MvPolynomial σ ℚ_[p]) = 0 := by
  ext m
  simp [coeff_initPart]

noncomputable def grMap (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  ((LinearMap.mulLeft ℚ_[p] (X v ^ e : MvPolynomial σ ℚ_[p])).restrictScalars ℤ_[p]) ∘ₗ initL p v 0

theorem grMap_apply (v : σ) (e : ℕ) (h : MvPolynomial σ ℚ_[p]) : grMap p v e h = X v ^ e * initPart v 0 h := rfl

end Gen

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))

theorem wt_setLast (o j : ℕ) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt (setLast LL o) j c m = wt LL j c m := rfl

theorem glAct_setLast (o j : ℕ) (c d : Fin r) : glAct p (setLast LL o) j c d = glAct p LL j c d := rfl

theorem yCond_setLast [NeZero r] (o j : ℕ) (M : WithTop ℤ) :
    YCond p (r := r) (setLast LL o) j M = YCond p LL j M := rfl

theorem wtSpC_setLast (o j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    WtSpC p (setLast LL o) j Cs la = WtSpC p LL j Cs la := rfl

theorem hWC_setLast (o j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    HWC p (setLast LL o) j Cs la = HWC p LL j Cs la := rfl

theorem isoC_setLast (o j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p (setLast LL o) j Cs la = IsoC p LL j Cs la := rfl

theorem wt_pow (hv : LL.vec (Fin.last K) = true) (ρ c : Fin r) (e : ℕ) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL (K + 1) c (Finsupp.single (Fin.last K, ρ) e + m) = wt LL (K + 1) c m + (if ρ = c then (e : ℤ) else 0) := by
  unfold wt
  have hterm : ∀ i : Fin (K + 1),
      (if (i : ℕ) < K + 1 then (if LL.vec i then (((Finsupp.single (Fin.last K, ρ) e + m) (i, c) : ℕ) : ℤ)
        else -(((Finsupp.single (Fin.last K, ρ) e + m) (i, c) : ℕ) : ℤ)) else 0) =
      (if (i : ℕ) < K + 1 then (if LL.vec i then ((m (i, c) : ℕ) : ℤ) else -((m (i, c) : ℕ) : ℤ)) else 0) +
        (if i = Fin.last K then (if ρ = c then (e : ℤ) else 0) else 0) := by
    intro i
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hρ : ρ = c <;> simp [hv, Finsupp.single_apply, hρ] <;> (try ring)
    · simp [hi, Finsupp.single_apply, Ne.symm hi]
  refine (Finset.sum_congr rfl fun i _ => hterm i).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem multiDeg_pow (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last K)) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    MultiDeg LL (Finsupp.single (Fin.last K, ρ) e + m) ↔ MultiDeg (setLast LL (LL.deg (Fin.last K) - e)) m := by
  have hsum : ∀ i, ∑ c, (Finsupp.single (Fin.last K, ρ) e + m) (i, c) =
      ∑ c, m (i, c) + (if i = Fin.last K then e else 0) := by
    intro i
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Prod.mk.injEq]
    by_cases hi : i = Fin.last K
    · subst hi
      simp [add_comm]
    · simp [Ne.symm hi, hi]
  unfold MultiDeg setLast
  constructor
  · intro h i
    have h1 := h i
    rw [hsum] at h1
    simp only [Function.update_apply]
    split_ifs with hi
    · subst hi
      simp only [if_true] at h1
      omega
    · simp only [hi, if_false, add_zero] at h1
      exact h1
  · intro h i
    have h1 := h i
    simp only [Function.update_apply] at h1
    rw [hsum]
    split_ifs at h1 with hi
    · subst hi
      simp only [if_true]
      omega
    · simp only [hi, if_false, add_zero]
      exact h1

theorem pol_pow (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last K)) (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ Pol p r LL ↔ h ∈ Pol p r (setLast LL (LL.deg (Fin.last K) - e)) := by
  unfold Pol
  rw [pow_mul_mem]
  have hset : {m | Finsupp.single (Fin.last K, ρ) e + m ∈ {m | MultiDeg LL m}} =
      {m | MultiDeg (setLast LL (LL.deg (Fin.last K) - e)) m} := by
    ext m
    simp only [Set.mem_setOf_eq]
    exact multiDeg_pow LL ρ e he m
  rw [hset]

theorem wtSpC_pow (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e o : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ WtSpC p LL (K + 1) Cs w ↔
      h ∈ WtSpC p (setLast LL o) (K + 1) Cs (shiftWt w ρ e) := by
  unfold WtSpC
  rw [pow_mul_mem]
  have hset : {m | Finsupp.single (Fin.last K, ρ) e + m ∈ {m | ∀ c ∈ Cs, wt LL (K + 1) c m = w c}} =
      {m | ∀ c ∈ Cs, wt (setLast LL o) (K + 1) c m = shiftWt w ρ e c} := by
    ext m
    simp only [Set.mem_setOf_eq, wt_setLast, wt_pow LL hv, shiftWt, Function.update_apply]
    refine forall₂_congr fun c _ => ?_
    by_cases hc : c = ρ
    · subst hc
      rw [if_pos rfl, if_pos rfl]
      omega
    · rw [if_neg (Ne.symm hc), if_neg hc, add_zero]
  rw [hset]

theorem glAct_pow (hv : LL.vec (Fin.last K) = true) (ρ c d : Fin r) (hd : d ≠ ρ) (e : ℕ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    glAct p LL (K + 1) c d (X (Fin.last K, ρ) ^ e * h) = X (Fin.last K, ρ) ^ e * glAct p LL (K + 1) c d h := by
  have hd0 : ∀ (i : Fin (K + 1)) (b : Fin r), (i, b) ≠ (Fin.last K, ρ) →
      pderiv (i, b) (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) = 0 := by
    intro i b hne
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (Ne.symm hne), smul_zero, smul_zero]
  unfold glAct
  simp only [LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz, hd0 i d (fun h => hd (Prod.mk.inj h).2), smul_zero, add_zero, smul_eq_mul]
    ring
  · have hi : i ≠ Fin.last K := by
      rintro rfl
      rw [hv] at h2
      exact h2 rfl
    simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
    rw [Derivation.leibniz, hd0 i c (fun h => hi (Prod.mk.inj h).1), smul_zero, add_zero, smul_eq_mul]
    ring
  · simp

theorem hWC_pow (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e o : ℕ) (w : Fin r → ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ HWC p LL (K + 1) (univ.erase ρ) w ↔
      h ∈ HWC p (setLast LL o) (K + 1) (univ.erase ρ) (shiftWt w ρ e) := by
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, wtSpC_pow LL hv ρ e o,
    glAct_setLast]
  refine and_congr Iff.rfl (forall_congr' fun c => forall_congr' fun d => forall_congr' fun hcd => ?_)
  rw [glAct_pow LL hv ρ c d (Finset.ne_of_mem_erase hcd.2.1) e h]
  constructor
  · intro h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (X_ne_zero _))
  · intro h0
    rw [h0, mul_zero]

theorem yCond_pow [NeZero r] (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e j : ℕ) (M : WithTop ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ YCond p LL j M ↔
      h ∈ YCond p LL j (if K + 1 ≤ j then M + ((-(e : ℤ) : ℤ) : WithTop ℤ) else M) := by
  by_cases hj : K + 1 ≤ j
  · rw [if_pos hj]
    induction e generalizing M with
    | zero => simp
    | succ e ih =>
      rw [pow_succ', mul_assoc, mul_last_letter_holds p K r LL j M ρ _ hj hv, ih, add_assoc, ← WithTop.coe_add]
      have : (-1 : ℤ) + -(e : ℤ) = -((e + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]
  · rw [if_neg hj]
    induction e with
    | zero => simp
    | succ e ih => rw [pow_succ', mul_assoc, mul_early_letters_holds p K r LL j M ρ _ (by omega), ih]

theorem mMw_pow [NeZero r] (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ) (he : e ≤ LL.deg (Fin.last K))
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ MMw p LL J M ρ w ↔
      h ∈ MMw p (setLast LL (LL.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) := by
  simp only [MMw, Y, Submodule.mem_inf, Submodule.mem_iInf, pol_pow LL ρ e he, yCond_pow LL hv ρ e,
    hWC_pow LL hv ρ e (LL.deg (Fin.last K) - e), wtSpC_pow LL hv ρ e (LL.deg (Fin.last K) - e),
    yCond_setLast, shiftLastLetterThresholds]

theorem mMwZ_pow [NeZero r] (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ) (he : e ≤ LL.deg (Fin.last K))
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ MMwZ p LL J M ρ w ↔
      h ∈ MMwZ p (setLast LL (LL.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) := by
  simp only [MMwZ, Submodule.mem_inf, Submodule.restrictScalars_mem, mMw_pow LL hv J M ρ w e he,
    pow_mul_int_iff]

end Last

theorem filtration_eq_holds : FilEq := by
  intro p _ K r _ LLw q J M ρ w e hv he f
  simp only [FilE, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨hZ, hS⟩
    obtain ⟨h, rfl⟩ := exists_pow_div _ e f hS
    exact ⟨h, (mMwZ_pow LLw hv J M ρ w e he h).mp hZ, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(mMwZ_pow LLw hv J M ρ w e he h).mpr hh, pow_mul_order _ e h⟩

theorem filtration_bot_holds : FilBot := by
  intro p _ K r _ LLw q J M ρ w e he
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  simp only [FilE, MMwZ, MMw, Y, Submodule.mem_inf, Submodule.restrictScalars_mem] at hf
  obtain ⟨⟨⟨⟨⟨hPol, _⟩, _⟩, _⟩, _⟩, hS⟩ := hf
  rw [Pol, mem_restrictSupport_iff] at hPol
  rw [mem_restrictSupport_iff] at hS
  ext m
  rw [coeff_zero]
  by_contra hne
  have h1 : MultiDeg LLw m := hPol (mem_support_iff.mpr hne)
  have h2 : e ≤ m (Fin.last K, ρ) := hS (mem_support_iff.mpr hne)
  have h3 : m (Fin.last K, ρ) ≤ ∑ c, m (Fin.last K, c) :=
    Finset.single_le_sum (f := fun c => m (Fin.last K, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)
  have h4 := h1 (Fin.last K)
  omega

theorem graded_eq_holds : GrEq := by
  intro p _ K r _ LLw q J M ρ w e hv he x
  have hset : (initPart (Fin.last K, ρ) e '' (FilE p LLw J M ρ w (Fin.last K, ρ) e :
      Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))) =
      ((MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e)).map
        (grMap p (Fin.last K, ρ) e) : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, grMap_apply]
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨h, hh, rfl⟩ := (filtration_eq_holds p K r LLw J M ρ w e hv he f).mp hf
      exact ⟨h, hh, (initPart_pow_mul _ e h).symm⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨X (Fin.last K, ρ) ^ e * h,
        (filtration_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, rfl⟩, initPart_pow_mul _ e h⟩
  unfold grLat
  rw [hset, Submodule.span_eq]
  simp only [Submodule.mem_map, grMap_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem graded_bot_holds : GrBot := by
  intro p _ K r _ LLw q J M ρ w e he
  have hF := filtration_bot_holds p K r LLw J M ρ w e he
  unfold grLat
  rw [hF]
  simp [initPart_zero']

end Formalism.InvariantFactorPaths.L4
