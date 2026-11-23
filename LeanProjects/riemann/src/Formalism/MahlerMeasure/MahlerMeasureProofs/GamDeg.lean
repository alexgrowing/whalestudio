import Formalism.MahlerMeasure.HasOrder
import Formalism.MahlerMeasure.FinalM
import Formalism.MahlerMeasure.MahlerMeasureProofs.FreezeInto

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable {R σ : Type} [CommSemiring R]

theorem pderiv_comm' (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on
  · simp
  · rename_i p q hp hq; simp only [map_add, hp, hq]
  · rename_i p n hp
    have h0 : ∀ a b : σ, pderiv a (Pi.single (M := fun _ => MvPolynomial σ R) b 1 n) = 0 := by
      intro a b; rw [Pi.single_apply]; split_ifs <;> simp
    simp only [Derivation.leibniz, map_add, smul_eq_mul, pderiv_X, h0, hp, mul_zero, zero_add, add_zero]
    ring

noncomputable abbrev Dp (v : σ) : Module.End R (MvPolynomial σ R) := (pderiv v).toLinearMap

theorem Dp_apply (v : σ) (p : MvPolynomial σ R) : Dp v p = pderiv v p := rfl

theorem pow_Dp_mul (v : σ) (a b : MvPolynomial σ R) (m : ℕ) :
    (Dp v ^ m) (a * b) = ∑ i ∈ range (m + 1), m.choose i • ((Dp v ^ i) a * (Dp v ^ (m - i)) b) := by
  have hl : ∀ x y : MvPolynomial σ R, Dp v (x * y) = x * Dp v y + y * Dp v x := fun x y => by
    simp only [Dp_apply, Derivation.leibniz, smul_eq_mul]
  have hs : ∀ (j : ℕ) (x : MvPolynomial σ R), (Dp v ^ (j + 1)) x = Dp v ((Dp v ^ j) x) := by
    intro j x; rw [pow_succ'] <;> rfl
  have key : ∀ n, (Dp v ^ n) (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • ((Dp v ^ ij.1) a * (Dp v ^ ij.2) b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => (Dp v ^ i) a * (Dp v ^ j) b), hs, ih, map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hsym : n.choose ij.2 = n.choose ij.1 := by rw [← hij, Nat.choose_symm_add]
      beta_reduce
      rw [map_nsmul, hl, hs, hs, hsym]
      ring
  rw [key, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i • ((Dp v ^ i) a * (Dp v ^ j) b))]

theorem pow_Dp_monomial (v : σ) (s : σ →₀ ℕ) (c : R) (k : ℕ) :
    (Dp v ^ k) (monomial s c) = monomial (s - Finsupp.single v k) (c * ((s v).descFactorial k : R)) := by
  classical
  induction k generalizing s c with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    show (Dp v ^ k) (Dp v (monomial s c)) = _
    rw [Dp_apply, pderiv_monomial, ih]
    have h1 : s - Finsupp.single v 1 - Finsupp.single v k = s - Finsupp.single v (k + 1) := by
      ext x; simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega
    have h2 : c * ((s v : ℕ) : R) * ((((s - Finsupp.single v 1 : σ →₀ ℕ) v).descFactorial k : ℕ) : R) =
        c * (((s v).descFactorial (k + 1) : ℕ) : R) := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      rcases Nat.eq_zero_or_pos (s v) with h | h
      · simp [h]
      · obtain ⟨m, hm⟩ : ∃ m, s v = m + 1 := ⟨s v - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, Nat.succ_descFactorial_succ]; push_cast; ring
    rw [h1, h2]

theorem pow_Dp_X_pow (v : σ) (m t : ℕ) :
    (Dp v ^ t) (X v ^ m : MvPolynomial σ R) = m.descFactorial t • X v ^ (m - t) := by
  rw [X_pow_eq_monomial, pow_Dp_monomial, Finsupp.single_eq_same, ← Finsupp.single_tsub,
    X_pow_eq_monomial, one_mul, smul_monomial, nsmul_eq_mul, mul_one]

theorem pow_Dp_eq_zero (v : σ) (q : MvPolynomial σ R) (K : ℕ) (hq : ∀ s ∈ q.support, s v ≤ K) :
    (Dp v ^ (K + 1)) q = 0 := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [pow_Dp_monomial, (Nat.descFactorial_eq_zero_iff_lt).2 (Nat.lt_succ_of_le (hq s hs))]
  simp

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

noncomputable def fw (m : σ →₀ ℕ) : ℚ_[p] := m.prod fun _ k => (k.factorial : ℚ_[p])

theorem fw_eq (m : σ →₀ ℕ) : fw p m = ∏ x, ((m x).factorial : ℚ_[p]) := by
  rw [fw, Finsupp.prod_fintype _ _ (fun _ => by simp)]

theorem fw_add_single (m : σ →₀ ℕ) (v : σ) :
    fw p (m + Finsupp.single v 1) = fw p m * ((m v + 1 : ℕ) : ℚ_[p]) := by
  rw [fw_eq, fw_eq]
  have key : ∀ x, (((m + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℚ_[p]) =
      ((m x).factorial : ℚ_[p]) * (if x = v then ((m v + 1 : ℕ) : ℚ_[p]) else 1) := by
    intro x
    by_cases h : x = v
    · subst h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, if_true, Nat.factorial_succ, Nat.cast_mul]
      ring
    · simp [Finsupp.single_apply, Ne.symm h, h]
  simp_rw [key, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem fock_eq_sum (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * fw p m := by
  simp only [M.fock, fw]
  refine Finset.sum_subset hs fun m _ hm => ?_
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_comm (F G : MvPolynomial σ ℚ_[p]) : M.fock p F G = M.fock p G F := by
  rw [fock_eq_sum p F G (F.support ∪ G.support) (fun x hx => Finset.mem_union_left _ hx),
    fock_eq_sum p G F (F.support ∪ G.support) (fun x hx => Finset.mem_union_right _ hx)]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem fock_eq_sum' (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * fw p m := by
  rw [fock_comm, fock_eq_sum p G F s hs]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem fock_add_left (F F' G : MvPolynomial σ ℚ_[p]) :
    M.fock p (F + F') G = M.fock p F G + M.fock p F' G := by
  rw [fock_eq_sum' p _ G G.support (Finset.Subset.refl _), fock_eq_sum' p F G G.support (Finset.Subset.refl _),
    fock_eq_sum' p F' G G.support (Finset.Subset.refl _), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by rw [coeff_add]; ring

theorem fock_smul_left (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p (c • F) G = c * M.fock p F G := by
  rw [fock_eq_sum' p _ G G.support (Finset.Subset.refl _), fock_eq_sum' p F G G.support (Finset.Subset.refl _),
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [coeff_smul, smul_eq_mul]; ring

theorem fock_zero_left (G : MvPolynomial σ ℚ_[p]) : M.fock p 0 G = 0 := by
  rw [fock_eq_sum' p 0 G G.support (Finset.Subset.refl _)]
  simp

theorem fock_sum_left {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    M.fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, M.fock p (F i) G := by
  classical
  refine Finset.induction_on t (by simp [fock_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]

theorem fock_add_right (F G G' : MvPolynomial σ ℚ_[p]) :
    M.fock p F (G + G') = M.fock p F G + M.fock p F G' := by
  rw [fock_comm p F (G + G'), fock_add_left, fock_comm p G F, fock_comm p G' F]

theorem fock_smul_right (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p F (c • G) = c * M.fock p F G := by
  rw [fock_comm p F (c • G), fock_smul_left, fock_comm p G F]

theorem fock_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, M.fock p F (G i) := by
  rw [fock_comm, fock_sum_left]
  exact Finset.sum_congr rfl fun i _ => fock_comm p _ _

private theorem coeff_pderiv_lemma_7 (v : σ) (b : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    coeff m (pderiv v b) = coeff (m + Finsupp.single v 1) b * ((m v + 1 : ℕ) : ℚ_[p]) := by
  induction b using MvPolynomial.induction_on'
  · rename_i t d
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : t = m + Finsupp.single v 1
    · subst h
      rw [if_pos (add_tsub_cancel_right m _), if_pos rfl]
      simp
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have ht : t v = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hne))]
        simp [ht]
      · rfl
  · rename_i f g hf hg
    rw [map_add, coeff_add, coeff_add, hf, hg, add_mul]

theorem fock_X_mul (v : σ) (a b : MvPolynomial σ ℚ_[p]) :
    M.fock p (X v * a) b = M.fock p a (pderiv v b) := by
  have hsupp : (X v * a).support ⊆ a.support.map (addRightEmbedding (Finsupp.single v 1)) := by
    rw [mul_comm, support_mul_X] <;> exact Finset.Subset.refl _
  rw [fock_eq_sum p _ b _ hsupp, Finset.sum_map, fock_eq_sum p a _ a.support (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addRightEmbedding_apply]
  rw [mul_comm (X v) a, coeff_mul_X, coeff_pderiv_lemma_7, fw_add_single]
  ring

theorem fock_X_pow_mul (v : σ) (k : ℕ) (a b : MvPolynomial σ ℚ_[p]) :
    M.fock p (X v ^ k * a) b = M.fock p a ((Dp v ^ k) b) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    have h1 : (Dp v ^ (k + 1)) b = Dp v ((Dp v ^ k) b) := by rw [pow_succ'] <;> rfl
    rw [h1, pow_succ, mul_assoc, ih, fock_X_mul, Dp_apply]

variable {r : ℕ} (w e : Fin r → σ)

theorem fock_E (a b : MvPolynomial σ ℚ_[p]) :
    M.fock p (tieE w e a) b = M.fock p a (tieF w e b) := by
  have hF : tieF w e b = ∑ c, pderiv (w c) (pderiv (e c) b) := by simp [tieF, LinearMap.sum_apply]
  simp only [tieE, LinearMap.mulLeft_apply, Finset.sum_mul, fock_sum_left]
  rw [hF, fock_sum_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc, fock_X_mul, fock_X_mul, pderiv_comm' (e c) (w c)]

theorem fock_E_pow (j : ℕ) (a b : MvPolynomial σ ℚ_[p]) :
    M.fock p ((tieE w e ^ j) a) b = M.fock p a ((tieF w e ^ j) b) := by
  induction j generalizing b with
  | zero => simp
  | succ j ih =>
    have h1 : (tieE w e ^ (j + 1)) a = tieE w e ((tieE w e ^ j) a) := by rw [pow_succ'] <;> rfl
    have h2 : (tieF w e ^ (j + 1)) b = (tieF w e ^ j) (tieF w e b) := by rw [pow_succ] <;> rfl
    rw [h1, h2, fock_E, ih]

theorem fock_phi_symm (o n z : ℕ) (u v : MvPolynomial σ ℚ_[p]) :
    M.fock p (tiePhi w e o n z u) v = M.fock p (tiePhi w e o n z v) u := by
  simp only [tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [fock_sum_left, fock_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fock_smul_left, fock_smul_left, fock_E_pow, fock_E_pow, fock_comm]

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

noncomputable def EW (w : Fin r → σ) (g : MvPolynomial σ k) : MvPolynomial σ k := ∑ c, X (w c) * pderiv (w c) g

theorem EW_add_single (hwe : ∀ c d, w c ≠ e d) (c : Fin r) (g : MvPolynomial σ k) :
    EW w (pderiv (e c) g) = pderiv (e c) (EW w g) := by
  classical
  simp only [EW, map_sum, Derivation.leibniz, pderiv_X, smul_eq_mul]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Pi.single_apply, if_neg (hwe c' c), pderiv_comm' (w c') (e c)]
  simp

theorem EW_pderiv_w (hw : Function.Injective w) (c : Fin r) (g : MvPolynomial σ k) :
    EW w (pderiv (w c) g) = pderiv (w c) (EW w g) - pderiv (w c) g := by
  classical
  have h : pderiv (w c) (EW w g) = EW w (pderiv (w c) g) + pderiv (w c) g := by
    simp only [EW, map_sum, Derivation.leibniz, pderiv_X, smul_eq_mul, Pi.single_apply, hw.eq_iff]
    rw [Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun c' _ => by rw [pderiv_comm' (w c) (w c')]
    · simp
  rw [h]; ring

private theorem tieF_apply_lemma (g : MvPolynomial σ k) :
    tieF w e g = ∑ c, pderiv (w c) (pderiv (e c) g) := by
  simp [tieF, LinearMap.sum_apply]

private theorem EW_sum_lemma_2 (s : Finset (Fin r)) (f : Fin r → MvPolynomial σ k) :
    EW w (∑ c ∈ s, f c) = ∑ c ∈ s, EW w (f c) := by
  simp only [EW, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem EW_F (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (g : MvPolynomial σ k)
    (h : EW w g = α • g) : EW w (tieF w e g) = (α - 1) • tieF w e g := by
  rw [tieF_apply_lemma, EW_sum_lemma_2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [EW_pderiv_w hw, EW_add_single hwe, h, Derivation.map_smul, Derivation.map_smul, sub_smul, one_smul]

theorem EH_F (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (β : k) (g : MvPolynomial σ k)
    (h : EW e g = β • g) : EW e (tieF w e g) = (β - 1) • tieF w e g := by
  have hs : tieF w e g = tieF e w g := by
    rw [tieF_apply_lemma, tieF_apply_lemma]
    exact Finset.sum_congr rfl fun c _ => pderiv_comm' _ _ _
  rw [hs]
  exact EW_F he (fun c d => (hwe d c).symm) β g h

theorem E_swap (g : MvPolynomial σ k) : tieE w e g = tieE e w g := by
  simp only [tieE, LinearMap.mulLeft_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem F_E_k (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (α β : k) (Y : MvPolynomial σ k) (hW : EW w Y = α • Y) (hE : EW e Y = β • Y) :
    tieF w e (tieE w e Y) = tieE w e (tieF w e Y) + (α + β + r) • Y := by
  classical
  have hdE : ∀ c, pderiv (e c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (w c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, he.eq_iff, hwe]
  have hdW : ∀ c, pderiv (w c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (e c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, hw.eq_iff, fun a b => (hwe a b).symm]
  have key : ∀ c, pderiv (w c) (pderiv (e c) ((∑ c', X (w c') * X (e c')) * Y)) =
      (∑ c', X (w c') * X (e c')) * pderiv (w c) (pderiv (e c) Y) + X (e c) * pderiv (e c) Y + Y +
        X (w c) * pderiv (w c) Y := by
    intro c
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hdE, hdW, pderiv_X, Pi.single_eq_same]
    ring
  rw [tieF_apply_lemma, tieF_apply_lemma]
  simp only [tieE, LinearMap.mulLeft_apply]
  simp only [key]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ c, X (e c) * pderiv (e c) Y = β • Y := hE
  have h2 : ∑ c, X (w c) * pderiv (w c) Y = α • Y := hW
  rw [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_smul, add_smul,
    ← Nat.cast_smul_eq_nsmul k]
  abel

theorem EW_Fpow (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (g : MvPolynomial σ k)
    (h : EW w g = α • g) (j : ℕ) : EW w ((tieF w e ^ j) g) = (α - j) • (tieF w e ^ j) g := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [pow_succ']
    show EW w (tieF w e ((tieF w e ^ j) g)) = _ • tieF w e ((tieF w e ^ j) g)
    rw [EW_F hw hwe (α - j) _ ih]
    congr 1; push_cast; ring

theorem EH_Fpow (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (β : k) (g : MvPolynomial σ k)
    (h : EW e g = β • g) (j : ℕ) : EW e ((tieF w e ^ j) g) = (β - j) • (tieF w e ^ j) g := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [pow_succ']
    show EW e (tieF w e ((tieF w e ^ j) g)) = _ • tieF w e ((tieF w e ^ j) g)
    rw [EH_F he hwe (β - j) _ ih]
    congr 1; push_cast; ring

theorem Fpow_E (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (α β : k) (Z : MvPolynomial σ k) (hW : EW w Z = α • Z) (hE : EW e Z = β • Z) (j : ℕ) :
    (tieF w e ^ (j + 1)) (tieE w e Z) =
      tieE w e ((tieF w e ^ (j + 1)) Z) + (((j : k) + 1) * (α + β + r - j)) • (tieF w e ^ j) Z := by
  induction j with
  | zero => simpa using F_E_k hw he hwe α β Z hW hE
  | succ j ih =>
    have hs : ∀ (i : ℕ) (x : MvPolynomial σ k), (tieF w e ^ (i + 1)) x = tieF w e ((tieF w e ^ i) x) := by
      intro i x; rw [pow_succ'] <;> rfl
    rw [hs (j + 1), ih, map_add, map_smul, F_E_k hw he hwe (α - ((j + 1 : ℕ) : k)) (β - ((j + 1 : ℕ) : k)) _
      (EW_Fpow hw hwe α Z hW (j + 1)) (EH_Fpow he hwe β Z hE (j + 1)), ← hs (j + 1), ← hs j]
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

private theorem X_mul_pderiv_monomial_lemma_3 (v : σ) (t : σ →₀ ℕ) (c : k) :
    X v * pderiv v (monomial t c) = monomial t (c * (t v : k)) := by
  classical
  rw [pderiv_monomial]
  by_cases ht : t v = 0
  · simp [ht]
  · rw [MvPolynomial.X, monomial_mul, one_mul]
    have h1 : Finsupp.single v 1 + (t - Finsupp.single v 1) = t := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hx
      · subst hx; omega
      · omega
    rw [h1]

private theorem coeff_X_mul_pderiv_lemma_4 (v : σ) (g : MvPolynomial σ k) (s : σ →₀ ℕ) :
    coeff s (X v * pderiv v g) = (s v : k) * coeff s g := by
  classical
  induction g using MvPolynomial.induction_on'
  · rename_i t c
    rw [X_mul_pderiv_monomial_lemma_3, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · rename_i p q hp hq
    rw [map_add, mul_add, coeff_add, hp, hq, coeff_add]; ring

private theorem coeff_EW_lemma_5 (g : MvPolynomial σ k) (s : σ →₀ ℕ) :
    coeff s (EW w g) = ((∑ c, s (w c) : ℕ) : k) * coeff s g := by
  rw [EW, coeff_sum]
  simp only [coeff_X_mul_pderiv_lemma_4, Nat.cast_sum, Finset.sum_mul]

theorem eq_zero_of_EW (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) (h : EW w g = ((a : k) - b) • g) :
    g = 0 := by
  ext s
  have hs := congrArg (coeff s) h
  rw [coeff_EW_lemma_5, coeff_smul, smul_eq_mul] at hs
  have hne : ((∑ c, s (w c) : ℕ) : k) ≠ (a : k) - b := by
    intro heq
    have h2 : ((∑ c, s (w c) + b : ℕ) : k) = ((a : ℕ) : k) := by rw [Nat.cast_add, heq]; ring
    have h3 := Nat.cast_injective h2
    omega
  rw [coeff_zero]
  by_contra hc
  exact hne (mul_right_cancel₀ hc hs)

theorem tieE_pow_apply (j : ℕ) (g : MvPolynomial σ k) :
    (tieE w e ^ j) g = (∑ c, X (w c) * X (e c)) ^ j * g := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ']
    show tieE w e ((tieE w e ^ j) g) = _
    rw [ih]
    simp only [tieE, LinearMap.mulLeft_apply]
    ring

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

noncomputable def cph (k : Type) [Field k] (A j : ℕ) : k :=
  ((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((A.choose j : ℕ) : k))

theorem cph_step (B t o' n' z : ℕ) (hB : B = o' + n' + r + z) (ht : t ≤ o') :
    cph k (B + 1) t + cph k (B + 1) (t + 1) * (((t : k) + 1) * ((o' : k) + n' + r - t)) =
      ((z : k) + 1) / ((B + 1 : ℕ) : k) * cph k B t := by
  have htB : t ≤ B := by omega
  have hc : ((B.choose t : ℕ) : k) ≠ 0 := by exact_mod_cast (Nat.choose_pos htB).ne'
  have ht1 : (t : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero t
  have hB1 : (B : k) + 1 ≠ 0 := Nat.cast_add_one_ne_zero B
  have hf : (t.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hne : (B : k) + 1 - t ≠ 0 := by
    rw [← Nat.cast_add_one, ← Nat.cast_sub (by omega : t ≤ B + 1)]
    exact_mod_cast (by omega : B + 1 - t ≠ 0)
  have hd : (((B + 1).choose (t + 1) : ℕ) : k) = ((B : k) + 1) * (B.choose t : k) / ((t : k) + 1) := by
    rw [eq_div_iff ht1]
    have h := Nat.add_one_mul_choose_eq B t
    exact_mod_cast h.symm
  have he : (((B + 1).choose t : ℕ) : k) = ((B : k) + 1) * (B.choose t : k) / ((B : k) + 1 - t) := by
    rw [eq_div_iff hne, ← Nat.cast_add_one, ← Nat.cast_sub (by omega : t ≤ B + 1)]
    have h := Nat.choose_mul_succ_eq B t
    exact_mod_cast (by rw [← h, mul_comm] : (B + 1).choose t * (B + 1 - t) = (B + 1) * B.choose t)
  have hB' : (o' : k) + n' + r = (B : k) - z := by rw [hB]; push_cast; ring
  simp only [cph, hd, he, hB', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end

section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

theorem tiePhi_eq (o n z : ℕ) (u : MvPolynomial σ k) :
    tiePhi w e o n z u = ∑ j ∈ range (o + 1), cph k (o + n + r + z - 1) j • (tieE w e ^ j) ((tieF w e ^ j) u) := by
  first
  | (simp only [tiePhi, cph, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]; done)
  | simp [tiePhi, cph, LinearMap.sum_apply]

theorem phi_E_step (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (o' n' z : ℕ) (Z : MvPolynomial σ k) (hW : EW w Z = (o' : k) • Z) (hE : EW e Z = (n' : k) • Z) :
    tiePhi w e (o' + 1) (n' + 1) z (tieE w e Z) =
      (((z : k) + 1) / ((o' + n' + r + z + 1 : ℕ) : k)) • tieE w e (tiePhi w e o' n' (z + 1) Z) := by
  have hE2 : ∀ (t : ℕ) (x : MvPolynomial σ k), tieE w e ((tieE w e ^ t) x) = (tieE w e ^ (t + 1)) x := by
    intro t x; rw [pow_succ'] <;> rfl
  have hE1 : ∀ (t : ℕ) (x : MvPolynomial σ k), (tieE w e ^ t) (tieE w e x) = (tieE w e ^ (t + 1)) x := by
    intro t x; rw [pow_succ] <;> rfl
  have hvan : (tieF w e ^ (o' + 1)) Z = 0 :=
    eq_zero_of_EW (w := w) o' (o' + 1) (by omega) _ (EW_Fpow hw hwe (o' : k) Z hW (o' + 1))
  have hG : ∀ t : ℕ, (tieE w e ^ (t + 1)) ((tieF w e ^ (t + 1)) (tieE w e Z)) =
      (tieE w e ^ (t + 1 + 1)) ((tieF w e ^ (t + 1)) Z) +
        (((t : k) + 1) * ((o' : k) + n' + r - t)) • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z) := by
    intro t
    rw [Fpow_E hw he hwe (o' : k) (n' : k) Z hW hE t, map_add, map_smul, hE1]
  have hA1 : o' + 1 + (n' + 1) + r + z - 1 = o' + n' + r + z + 1 := by omega
  have hA2 : o' + n' + r + (z + 1) - 1 = o' + n' + r + z := by omega
  rw [tiePhi_eq, tiePhi_eq, hA1, hA2, map_sum, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_range_succ']
  beta_reduce
  simp only [hG, smul_add, smul_smul, Finset.sum_add_distrib, map_smul, hE2]
  have h0 : (tieE w e ^ 0) ((tieF w e ^ 0) (tieE w e Z)) = (tieE w e ^ (0 + 1)) ((tieF w e ^ 0) Z) := by simp
  rw [h0]
  have hs2 := Finset.sum_range_succ'
    (fun t => cph k (o' + n' + r + z + 1) t • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z)) (o' + 1)
  rw [Finset.sum_range_succ (fun t => cph k (o' + n' + r + z + 1) t • (tieE w e ^ (t + 1)) ((tieF w e ^ t) Z))
    (o' + 1)] at hs2
  beta_reduce at hs2
  rw [hvan, map_zero, smul_zero, add_zero] at hs2
  rw [add_right_comm, ← hs2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← add_smul, cph_step (o' + n' + r + z) t o' n' z rfl (by have := Finset.mem_range.1 ht; omega)]

end

section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

private theorem EW_E_lemma_8 (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d) (α : k) (Y : MvPolynomial σ k)
    (h : EW w Y = α • Y) : EW w (tieE w e Y) = (α + 1) • tieE w e Y := by
  classical
  have hdW : ∀ c, pderiv (w c) (∑ c', X (w c') * X (e c') : MvPolynomial σ k) = X (e c) := by
    intro c
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, hw.eq_iff, fun a b => (hwe a b).symm]
  have hEW : EW w Y = ∑ c, X (w c) * pderiv (w c) Y := rfl
  simp only [tieE, LinearMap.mulLeft_apply, EW, Derivation.leibniz, smul_eq_mul, hdW, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ c, X (w c) * ((∑ c', X (w c') * X (e c')) * pderiv (w c) Y) =
      (∑ c', X (w c') * X (e c')) * (α • Y) := by
    rw [← h, hEW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, X (w c) * (Y * X (e c)) = (∑ c', X (w c') * X (e c')) * Y := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [h1, h2, add_smul, one_smul, mul_smul_comm]

theorem phi_E_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) :
    ∀ (s o n z : ℕ) (Z : MvPolynomial σ k), s ≤ o → s ≤ n →
      EW w Z = ((o - s : ℕ) : k) • Z → EW e Z = ((n - s : ℕ) : k) • Z →
      tiePhi w e o n z ((tieE w e ^ s) Z) =
        (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) •
          (tieE w e ^ s) (tiePhi w e (o - s) (n - s) (z + s) Z) := by
  intro s
  induction s with
  | zero => intro o n z Z _ _ _ _; simp
  | succ s ih =>
    intro o n z Z hso hsn hW hE
    have hW' : EW w (tieE w e Z) = ((o - s : ℕ) : k) • tieE w e Z := by
      rw [EW_E_lemma_8 hw hwe _ Z hW]
      congr 1
      rw [show o - s = o - (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
    have hE' : EW e (tieE w e Z) = ((n - s : ℕ) : k) • tieE w e Z := by
      rw [E_swap, EW_E_lemma_8 he (fun c d => (hwe d c).symm) _ Z hE]
      congr 1
      rw [show n - s = n - (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
    have hE1 : (tieE w e ^ (s + 1)) Z = (tieE w e ^ s) (tieE w e Z) := by rw [pow_succ] <;> rfl
    rw [hE1, ih o n z (tieE w e Z) (by omega) (by omega) hW' hE']
    have ho : o - s = (o - (s + 1)) + 1 := by omega
    have hn : n - s = (n - (s + 1)) + 1 := by omega
    rw [ho, hn, phi_E_step hw he hwe (o - (s + 1)) (n - (s + 1)) (z + s) Z hW hE]
    rw [map_smul, smul_smul, Finset.prod_range_succ]
    have hE2 : (tieE w e ^ s) (tieE w e (tiePhi w e (o - (s + 1)) (n - (s + 1)) (z + s + 1) Z)) =
        (tieE w e ^ (s + 1)) (tiePhi w e (o - (s + 1)) (n - (s + 1)) (z + (s + 1)) Z) := by
      rw [← add_assoc]
      rw [pow_succ] <;> rfl
    rw [hE2]
    congr 2
    have h3 : o - (s + 1) + (n - (s + 1)) + r + (z + s) + 1 = o + n + r + z - 1 - s := by omega
    rw [h3]
    push_cast <;> ring

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

theorem sum_range_eq_of_zero {M : Type} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ)
    (ha : ∀ i, a ≤ i → f i = 0) (hb : ∀ i, b ≤ i → f i = 0) :
    ∑ i ∈ range a, f i = ∑ i ∈ range b, f i := by
  rcases le_total a b with h | h
  · exact Finset.sum_subset (Finset.range_subset_range.2 h) fun i _ hi => ha i (by simpa using hi)
  · exact (Finset.sum_subset (Finset.range_subset_range.2 h) fun i _ hi => hb i (by simpa using hi)).symm

section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}

theorem pow_Dp_omega (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (s i : ℕ) :
    (Dp (e ρ) ^ i) ((∑ c, X (w c) * X (e c)) ^ s : MvPolynomial σ k) =
      s.descFactorial i • (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i)) := by
  classical
  have hD : pderiv (e ρ) (∑ c, X (w c) * X (e c) : MvPolynomial σ k) = X (w ρ) := by
    simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, he.eq_iff, hwe]
  have hX : pderiv (e ρ) (X (w ρ) : MvPolynomial σ k) = 0 := by
    rw [pderiv_X, Pi.single_apply, if_neg (hwe ρ ρ)]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    show Dp (e ρ) ((Dp (e ρ) ^ i) _) = _
    rw [ih, map_nsmul, Dp_apply]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, hD, hX, smul_zero, add_zero, smul_eq_mul, nsmul_eq_mul,
      Nat.descFactorial_succ, Nat.cast_mul, Nat.sub_sub, mul_zero]
    ring

theorem pow_Dp_omega_mul (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (s m : ℕ)
    (V : MvPolynomial σ k) :
    (Dp (e ρ) ^ m) ((∑ c, X (w c) * X (e c)) ^ s * V) =
      ∑ i ∈ range (s + 1), (m.choose i * s.descFactorial i) •
        (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) * (Dp (e ρ) ^ (m - i)) V) := by
  rw [pow_Dp_mul]
  have hfe : ∀ i, m.choose i • ((Dp (e ρ) ^ i) ((∑ c, X (w c) * X (e c)) ^ s) * (Dp (e ρ) ^ (m - i)) V) =
      (m.choose i * s.descFactorial i) •
        (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) * (Dp (e ρ) ^ (m - i)) V) := by
    intro i
    rw [pow_Dp_omega he hwe, smul_mul_assoc, smul_smul]
  simp only [hfe]
  exact sum_range_eq_of_zero _ (m + 1) (s + 1)
    (fun i hi => by simp [Nat.choose_eq_zero_of_lt (show m < i by omega)])
    (fun i hi => by simp [Nat.descFactorial_eq_zero_iff_lt.2 (show s < i by omega)])

theorem pow_Dp_X_pow_mul (v : σ) (q : MvPolynomial σ k) (K M m : ℕ) (hq : ∀ s ∈ q.support, s v ≤ K) :
    (Dp v ^ M) (q * X v ^ m) =
      ∑ i ∈ range (K + 1), (M.choose i * m.descFactorial (M - i)) • ((Dp v ^ i) q * X v ^ (m - (M - i))) := by
  have hz : ∀ i, K + 1 ≤ i → (Dp v ^ i) q = 0 := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [show K + 1 + d = d + (K + 1) by ring, pow_add]
    show (Dp v ^ d) ((Dp v ^ (K + 1)) q) = 0
    rw [pow_Dp_eq_zero v q K hq, map_zero]
  rw [pow_Dp_mul]
  have hfe : ∀ i, M.choose i • ((Dp v ^ i) q * (Dp v ^ (M - i)) (X v ^ m)) =
      (M.choose i * m.descFactorial (M - i)) • ((Dp v ^ i) q * X v ^ (m - (M - i))) := by
    intro i
    rw [pow_Dp_X_pow, mul_smul_comm, smul_smul]
  simp only [hfe]
  exact sum_range_eq_of_zero _ (M + 1) (K + 1)
    (fun i hi => by simp [Nat.choose_eq_zero_of_lt (show M < i by omega)])
    (fun i hi => by simp [hz i hi])

theorem Dp_comm_F (ρ : Fin r) (g : MvPolynomial σ k) : Dp (e ρ) (tieF w e g) = tieF w e (Dp (e ρ) g) := by
  rw [tieF_apply_lemma, tieF_apply_lemma]
  simp only [Dp_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pderiv_comm' (e ρ) (w c), pderiv_comm' (e ρ) (e c)]

theorem powDp_comm_powF (ρ : Fin r) (a b : ℕ) (g : MvPolynomial σ k) :
    (Dp (e ρ) ^ a) ((tieF w e ^ b) g) = (tieF w e ^ b) ((Dp (e ρ) ^ a) g) := by
  have h1 : ∀ (b : ℕ) (g : MvPolynomial σ k), Dp (e ρ) ((tieF w e ^ b) g) = (tieF w e ^ b) (Dp (e ρ) g) := by
    intro b
    induction b with
    | zero => intro g; simp
    | succ b ih =>
      intro g
      rw [pow_succ']
      show Dp (e ρ) (tieF w e ((tieF w e ^ b) g)) = tieF w e ((tieF w e ^ b) (Dp (e ρ) g))
      rw [Dp_comm_F, ih]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ']
    show Dp (e ρ) ((Dp (e ρ) ^ a) ((tieF w e ^ b) g)) = (tieF w e ^ b) (Dp (e ρ) ((Dp (e ρ) ^ a) g))
    rw [ih, h1]

theorem main_expand (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r) (q : MvPolynomial σ k)
    (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (s j m : ℕ) :
    (Dp (e ρ) ^ m) ((tieE w e ^ s) ((tieF w e ^ j) (X (e ρ) ^ m * q))) =
      (m.factorial : k) • ∑ i ∈ range (s + 1), ∑ t ∈ range (K + 1),
        (((m.choose i * (m - i).choose t : ℕ) : k) * (s.descFactorial i : k) / ((i + t).factorial : k)) •
          (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q)) := by
  rw [tieE_pow_apply, pow_Dp_omega_mul he hwe ρ s m, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [powDp_comm_powF, mul_comm (X (e ρ) ^ m) q, pow_Dp_X_pow_mul (e ρ) q K (m - i) m hq, map_sum,
    Finset.mul_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [map_nsmul, mul_smul_comm, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul k]
  by_cases him : i ≤ m
  · by_cases hit : t ≤ m - i
    · have he1 : m - (m - i - t) = i + t := by omega
      rw [he1, mul_comm ((Dp (e ρ) ^ t) q)]
      congr 1
      have hf := Nat.factorial_mul_descFactorial (show m - i - t ≤ m by omega)
      rw [he1] at hf
      have hne : ((i + t).factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      rw [← hf]
      push_cast
      first
      | (field_simp; ring)
      | field_simp
    · have h0 : (m - i).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
  · have h0 : m.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open Polynomial Finset

section
variable {k : Type} [Field k] [CharZero k]

def IsPD (N0 d : ℕ) (g : ℕ → k) : Prop :=
  ∃ P : Polynomial k, P.natDegree ≤ d ∧ ∀ n, N0 ≤ n → g n = P.eval (n : k)

theorem IsPD.mono {N0 d d' : ℕ} {g : ℕ → k} (h : IsPD N0 d g) (hd : d ≤ d') : IsPD N0 d' g := by
  obtain ⟨P, hP, hP'⟩ := h
  exact ⟨P, hP.trans hd, hP'⟩

theorem IsPD.const (N0 d : ℕ) (c : k) : IsPD N0 d (fun _ => c) := by
  exact ⟨Polynomial.C c, by simp, fun _ _ => by simp⟩

theorem IsPD.congr {N0 d : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (hg : ∀ n, N0 ≤ n → g' n = g n) :
    IsPD N0 d g' := by
  obtain ⟨P, hP, hP'⟩ := h
  exact ⟨P, hP, fun n hn => (hg n hn).trans (hP' n hn)⟩

theorem IsPD.add {N0 d : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (h' : IsPD N0 d g') :
    IsPD N0 d (fun n => g n + g' n) := by
  obtain ⟨P, hP, hP'⟩ := h
  obtain ⟨Q, hQ, hQ'⟩ := h'
  refine ⟨P + Q, (Polynomial.natDegree_add_le _ _).trans (max_le hP hQ), fun n hn => ?_⟩
  simp only [Polynomial.eval_add, hP' n hn, hQ' n hn]

theorem IsPD.mul {N0 d d' : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (h' : IsPD N0 d' g') :
    IsPD N0 (d + d') (fun n => g n * g' n) := by
  obtain ⟨P, hP, hP'⟩ := h
  obtain ⟨Q, hQ, hQ'⟩ := h'
  refine ⟨P * Q, Polynomial.natDegree_mul_le.trans (add_le_add hP hQ), fun n hn => ?_⟩
  simp only [Polynomial.eval_mul, hP' n hn, hQ' n hn]

theorem IsPD.sum {ι : Type} (t : Finset ι) {N0 d : ℕ} (g : ι → ℕ → k) (h : ∀ i ∈ t, IsPD N0 d (g i)) :
    IsPD N0 d (fun n => ∑ i ∈ t, g i n) := by
  classical
  revert h
  refine Finset.induction_on t ?_ ?_
  · intro _; simpa using IsPD.const N0 d (0 : k)
  · intro a s ha ih h
    simp only [Finset.sum_insert ha]
    exact IsPD.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsPD.choose_sub (S t : ℕ) : IsPD S t (fun n => (((n - S).choose t : ℕ) : k)) := by
  have hf : (t.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  refine ⟨Polynomial.C ((t.factorial : k)⁻¹) * (descPochhammer k t).comp (Polynomial.X - Polynomial.C (S : k)),
    (Polynomial.natDegree_C_mul_le _ _).trans (le_of_eq (by rw [Polynomial.natDegree_comp, descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one])), ?_⟩
  intro n hn
  have h1 : (n : k) - S = ((n - S : ℕ) : k) := by rw [Nat.cast_sub hn]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, h1,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]

theorem IsPD.choose_add (N0 c t : ℕ) : IsPD N0 t (fun n => (((n + c).choose t : ℕ) : k)) := by
  have hf : (t.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  refine ⟨Polynomial.C ((t.factorial : k)⁻¹) * (descPochhammer k t).comp (Polynomial.X + Polynomial.C (c : k)),
    (Polynomial.natDegree_C_mul_le _ _).trans (le_of_eq (by rw [Polynomial.natDegree_comp, descPochhammer_natDegree, Polynomial.natDegree_X_add_C, mul_one])), ?_⟩
  intro n _
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    ← Nat.cast_add, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]

theorem IsPD.choose_prod (S i t : ℕ) :
    IsPD S (i + t) (fun n => ((((n - S).choose i * (n - S - i).choose t : ℕ)) : k)) := by
  obtain ⟨P1, hd1, h1⟩ := IsPD.choose_sub (k := k) S i
  obtain ⟨P2, hd2, h2⟩ := IsPD.choose_sub (k := k) (S + i) t
  have h1' : ∀ n, S ≤ n → ((((n - S).choose i : ℕ)) : k) = P1.eval (n : k) := h1
  have h2' : ∀ n, S + i ≤ n → ((((n - S - i).choose t : ℕ)) : k) = P2.eval (n : k) := by
    intro n hn; rw [Nat.sub_sub]; exact h2 n hn
  refine ⟨P1 * P2, Polynomial.natDegree_mul_le.trans (add_le_add hd1 hd2), fun n hn => ?_⟩
  show ((((n - S).choose i * (n - S - i).choose t : ℕ)) : k) = _
  rw [Polynomial.eval_mul, ← h1' n hn]
  by_cases h : S + i ≤ n
  · rw [← h2' n h, Nat.cast_mul]
  · have h0 : (n - S).choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open Finset

section
variable {k : Type} [Field k] [CharZero k]

private theorem descF_add_lemma_6 (A a b : ℕ) :
    A.descFactorial (a + b) = A.descFactorial a * (A - a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ, Nat.sub_sub]
    ring

theorem coef_nat (A o s j : ℕ) (hsj : s + j ≤ o) :
    A.choose o * o.factorial =
      (A - s - j).choose (o - s - j) * (o - s - j).factorial * ((A - s).choose j * j.factorial) *
        A.descFactorial s := by
  have e1 : ∀ n m : ℕ, n.choose m * m.factorial = n.descFactorial m := fun n m => by
    rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
  rw [e1, e1, e1]
  have ho : o = s + (j + (o - s - j)) := by omega
  conv_lhs => rw [ho]
  rw [descF_add_lemma_6, descF_add_lemma_6, Nat.sub_sub]
  ring

theorem coef_PD (o r z s j S : ℕ) (hr : 1 ≤ r) (hsj : s + j ≤ o) (hoS : o ≤ S) :
    IsPD S (o - s - j) (fun n => (((o + n + r + z - 1).choose o : ℕ) : k) *
      (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) *
        cph k ((o - s) + (n - s) + r + (z + s) - 1) j) := by
  have hK := (IsPD.choose_add (k := k) S (o + r + z - 1 - s - j) (o - s - j)).mul
    (IsPD.const S 0 (((o - s - j).factorial : k) * (∏ i ∈ range s, ((z : k) + 1 + i)) * (-1) ^ j /
      ((o.factorial : k) * (j.factorial : k))))
  rw [add_zero] at hK
  refine hK.congr fun n hn => ?_
  beta_reduce
  have hA : (o - s) + (n - s) + r + (z + s) - 1 = o + n + r + z - 1 - s := by omega
  have hc : o + n + r + z - 1 - s - j = n + (o + r + z - 1 - s - j) := by omega
  have hnat := coef_nat (o + n + r + z - 1) o s j hsj
  rw [hc] at hnat
  have hprod : ∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k)) =
      (∏ i ∈ range s, ((z : k) + 1 + i)) / (((o + n + r + z - 1).descFactorial s : ℕ) : k) := by
    rw [Finset.prod_div_distrib, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [hA, hprod]
  have ho : (o.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero o
  have hj : (j.factorial : k) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hCj : (((o + n + r + z - 1 - s).choose j : ℕ) : k) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hD : (((o + n + r + z - 1).descFactorial s : ℕ) : k) ≠ 0 := by
    have : (o + n + r + z - 1).descFactorial s ≠ 0 := fun h0 => by
      rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
    exact_mod_cast this
  have hk := congrArg (Nat.cast : ℕ → k) hnat
  push_cast at hk
  have hX : (((o + n + r + z - 1).choose o : ℕ) : k) =
      ((n + (o + r + z - 1 - s - j)).choose (o - s - j) : k) * ((o - s - j).factorial : k) *
        (((o + n + r + z - 1 - s).choose j : k) * (j.factorial : k)) *
        ((o + n + r + z - 1).descFactorial s : k) / (o.factorial : k) := by
    rw [eq_div_iff ho]; exact hk
  rw [hX]
  simp only [cph]
  first
  | (field_simp; ring)
  | field_simp

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable {R σ : Type} [CommSemiring R]

theorem exists_X_pow_mul (v : σ) (e : ℕ) (f : MvPolynomial σ R) (hf : ∀ m ∈ f.support, e ≤ m v) :
    ∃ h : MvPolynomial σ R, f = X v ^ e * h ∧ ∀ m ∈ h.support, Finsupp.single v e + m ∈ f.support := by
  classical
  refine ⟨f.divMonomial (Finsupp.single v e), ?_, fun m hm => ?_⟩
  · have hmod : f.modMonomial (Finsupp.single v e) = 0 := by
      ext m
      rw [coeff_zero]
      by_cases h : Finsupp.single v e ≤ m
      · exact coeff_modMonomial_of_le f h
      · rw [coeff_modMonomial_of_not_le f h]
        by_contra hc
        exact h (Finsupp.single_le_iff.2 (hf m (mem_support_iff.2 hc)))
    conv_lhs => rw [← divMonomial_add_modMonomial f (Finsupp.single v e), hmod, add_zero]
    rw [X_pow_eq_monomial]
  · rw [mem_support_iff, coeff_divMonomial] at hm
    exact mem_support_iff.2 hm

end

section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

def lowerLast (LL : M.Letters (N + 1)) (e : ℕ) : M.Letters (N + 1) where
  vec := LL.vec
  deg := Function.update LL.deg (Fin.last N) (LL.deg (Fin.last N) - e)

theorem lowerLast_total (LL : M.Letters (N + 1)) (e : ℕ) (he : e ≤ LL.deg (Fin.last N)) :
    (lowerLast LL e).total = LL.total - e := by
  simp only [M.Letters.total, lowerLast, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last] <;> omega

theorem quot_mem_pol (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (f h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hf : f ∈ M.Pol p r LL) (hh : ∀ m ∈ h.support, Finsupp.single (Fin.last N, ρ) e + m ∈ f.support) :
    h ∈ M.Pol p r (lowerLast LL e) := by
  classical
  simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at hf ⊢
  intro m hm
  have h1 : M.MultiDeg LL (Finsupp.single (Fin.last N, ρ) e + m) := hf (hh m hm)
  show M.MultiDeg (lowerLast LL e) m
  intro i
  have h2 := h1 i
  have hs : ∑ c, (Finsupp.single (Fin.last N, ρ) e + m : Fin (N + 1) × Fin r →₀ ℕ) (i, c) =
      (if i = Fin.last N then e else 0) + ∑ c, m (i, c) := by
    simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    congr 1
    by_cases hi : i = Fin.last N
    · subst hi
      rw [Finset.sum_eq_single ρ]
      · simp
      · intro c _ hc; simp [Finsupp.single_apply, Ne.symm hc]
      · simp
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun c _ => by simp [Finsupp.single_apply, Ne.symm hi]
  rw [hs] at h2
  show ∑ c, m (i, c) = Function.update LL.deg (Fin.last N) (LL.deg (Fin.last N) - e) i
  by_cases hi : i = Fin.last N
  · subst hi; simp at h2 ⊢ <;> omega
  · simpa [hi] using h2

end

section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem weight_ind {K : ℕ} (b0 : Fin K) (m : Fin K × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin K × Fin r => (if x.1 = b0 then 1 else 0)) m = ∑ c, m (b0, c) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type_right]
  simp

theorem q_isWH (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hh : h ∈ M.Pol p r (lowerLast LL e)) (g : Fin (N + 1 + 1) → ℕ) :
    IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1) (aeval (M.freezeSub p LL ρ) h)
      (∑ b, (g (Fin.castSucc b) + g (Fin.last (N + 1))) * (lowerLast LL e).deg b) := by
  classical
  have hXX : ∀ (i : Fin (N + 1)) (c₁ c₂ : Fin r), IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (X (Fin.castSucc i, c₁) * X (Fin.last (N + 1), c₂) : MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p])
      (g (Fin.castSucc i) + g (Fin.last (N + 1))) := fun i c₁ c₂ =>
    (isWeightedHomogeneous_X ℚ_[p] _ _).mul (isWeightedHomogeneous_X ℚ_[p] _ _)
  have hXX' : ∀ (i : Fin (N + 1)) (c₁ c₂ : Fin r), IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (X (Fin.last (N + 1), c₂) * X (Fin.castSucc i, c₁) : MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p])
      (g (Fin.castSucc i) + g (Fin.last (N + 1))) := fun i c₁ c₂ => by
    rw [mul_comm]; exact hXX i c₁ c₂
  have hgen : ∀ x : Fin (N + 1) × Fin r, IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (M.freezeSub p LL ρ x) (g (Fin.castSucc x.1) + g (Fin.last (N + 1))) := by
    rintro ⟨i, c⟩
    simp only [M.freezeSub]
    split_ifs
    · exact IsWeightedHomogeneous.sum _ _ _ fun c' _ => hXX i c' c'
    · exact hXX' i c ρ
    · exact hXX' i ρ ρ
    · intro d hd
      rw [coeff_sub] at hd
      by_cases h1 : coeff d (X (Fin.last (N + 1), ρ) * X (Fin.castSucc i, c) :
          MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p]) = 0
      · rw [h1, zero_sub, neg_ne_zero] at hd
        exact hXX i ρ c hd
      · exact hXX' i c ρ h1
  have hsupp : ∀ m ∈ h.support, M.MultiDeg (lowerLast LL e) m := by
    have h2 := hh
    simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at h2
    exact fun m hm => h2 hm
  rw [h.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  rw [aeval_monomial]
  have hmd := hsupp m hm
  have hprod := IsWeightedHomogeneous.prod m.support (fun x => M.freezeSub p LL ρ x ^ m x)
    (fun x => m x • (g (Fin.castSucc x.1) + g (Fin.last (N + 1)))) (fun x _ => (hgen x).pow (m x))
  have hC := isWeightedHomogeneous_C (fun y : Fin (N + 1 + 1) × Fin r => g y.1) (coeff m h)
  have key : ∑ b, (g (Fin.castSucc b) + g (Fin.last (N + 1))) * (lowerLast LL e).deg b =
      0 + ∑ x ∈ m.support, m x • (g (Fin.castSucc x.1) + g (Fin.last (N + 1))) := by
    rw [zero_add, Finset.sum_subset (Finset.subset_univ m.support) (fun x _ hx => by
      rw [Finsupp.mem_support_iff, not_not] at hx; simp [hx])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hmd b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact hC.mul hprod

theorem degW_eq (LL : M.Letters (N + 1)) (e : ℕ) :
    ∑ b, ((fun b' : Fin (N + 1 + 1) => if b' = Fin.castSucc (Fin.last N) then 1 else 0) (Fin.castSucc b) +
      (fun b' : Fin (N + 1 + 1) => if b' = Fin.castSucc (Fin.last N) then 1 else 0) (Fin.last (N + 1))) *
        (lowerLast LL e).deg b = LL.deg (Fin.last N) - e := by
  have hne : Fin.last (N + 1) ≠ Fin.castSucc (Fin.last N) := (Fin.castSucc_lt_last _).ne'
  simp [lowerLast, hne, Fin.castSucc_inj]

theorem degH_eq (LL : M.Letters (N + 1)) (e : ℕ) (he : e ≤ LL.deg (Fin.last N)) :
    ∑ b, ((fun b' : Fin (N + 1 + 1) => if b' = Fin.last (N + 1) then 1 else 0) (Fin.castSucc b) +
      (fun b' : Fin (N + 1 + 1) => if b' = Fin.last (N + 1) then 1 else 0) (Fin.last (N + 1))) *
        (lowerLast LL e).deg b = LL.total - e := by
  first
  | (simp only [Fin.castSucc_ne_last, eq_self_iff_true, ↓reduceIte, zero_add, one_mul]
     rw [← lowerLast_total LL e he]; rfl)
  | (simp [Fin.castSucc_ne_last]; rw [← lowerLast_total LL e he]; rfl)

theorem Z_biHom (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) (m0 : ℕ) :
    BiHom (fun c : Fin r => (Fin.castSucc (Fin.last N), c)) (fun c : Fin r => (Fin.last (N + 1), c))
      (LL.deg (Fin.last N) - e) (m0 + (LL.total - e))
      (X (Fin.last (N + 1), ρ) ^ m0 * aeval (M.freezeSub p LL ρ) h) := by
  classical
  intro m hm
  rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul'] at hm
  split_ifs at hm with hle
  · rw [one_mul] at hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single (Fin.last (N + 1), ρ) m0 :=
      ⟨_, (tsub_add_cancel_of_le hle).symm⟩
    rw [add_tsub_cancel_right] at hm
    have hW : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r =>
        (if x.1 = Fin.castSucc (Fin.last N) then 1 else 0)) m' = LL.deg (Fin.last N) - e := by
      rw [← degW_eq LL e]
      exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.castSucc (Fin.last N) then 1 else 0) hm
    have hH : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r =>
        (if x.1 = Fin.last (N + 1) then 1 else 0)) m' = LL.total - e := by
      rw [← degH_eq LL e he]
      exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.last (N + 1) then 1 else 0) hm
    rw [weight_ind] at hW hH
    refine ⟨?_, ?_⟩
    · simp only [Finsupp.add_apply, Finset.sum_add_distrib, hW]
      simp [Finsupp.single_apply, (Fin.castSucc_lt_last (Fin.last N)).ne']
    · simp only [Finsupp.add_apply, Finset.sum_add_distrib, hH]
      simp [Finsupp.single_apply, add_comm]
  · exact absurd rfl hm

theorem q_etaDeg (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) :
    ∀ s ∈ (aeval (M.freezeSub p LL ρ) h).support, s (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro s hs
  have hw : Finsupp.weight (fun x : Fin (N + 1 + 1) × Fin r => (if x.1 = Fin.last (N + 1) then 1 else 0)) s =
      LL.total - e := by
    rw [← degH_eq LL e he]
    exact q_isWH p LL ρ e h hh (fun b' => if b' = Fin.last (N + 1) then 1 else 0) (mem_support_iff.1 hs)
  rw [weight_ind] at hw
  rw [← hw]
  exact Finset.single_le_sum (f := fun c => s (Fin.last (N + 1), c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM.GammaExpansion

open MvPolynomial Finset

section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem fock_expand (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r)
    (q y : MvPolynomial σ ℚ_[p]) (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (o' n' z' s m : ℕ) :
    M.fock p (X (e ρ) ^ m * y) ((tieE w e ^ s) (tiePhi w e o' n' z' (X (e ρ) ^ m * q))) =
      ∑ j ∈ range (o' + 1), cph ℚ_[p] (o' + n' + r + z' - 1) j * ((m.factorial : ℚ_[p]) *
        ∑ i ∈ range (s + j + 1), ∑ t ∈ range (K + 1),
          (((m.choose i * (m - i).choose t : ℕ) : ℚ_[p]) * ((s + j).descFactorial i : ℚ_[p]) /
            ((i + t).factorial : ℚ_[p])) *
          M.fock p y (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s + j - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q))) := by
  rw [fock_X_pow_mul, tiePhi_eq, map_sum, map_sum, fock_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hEE : (tieE w e ^ s) ((tieE w e ^ j) ((tieF w e ^ j) (X (e ρ) ^ m * q))) =
      (tieE w e ^ (s + j)) ((tieF w e ^ j) (X (e ρ) ^ m * q)) := by
    rw [pow_add] <;> rfl
  rw [map_smul, map_smul, hEE, main_expand he hwe ρ q K hq (s + j) j m, fock_smul_right, fock_smul_right,
    fock_sum_right]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fock_sum_right]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [fock_smul_right]

end

theorem alg_step {K : Type} [Field K] (a b c G Den I I' : K) (hG : G ≠ 0) (hD : Den ≠ 0)
    (hI : I' = I / Den) : a * (b * (c * (G * I))) / (G * Den) = a * b * c * I' := by
  subst hI
  first
  | (field_simp; ring)
  | field_simp

section
variable (p : ℕ) [Fact p.Prime]

theorem gam_oneSided (N r : ℕ) (LL : M.Letters (N + 1)) (ρ : Fin r) (z e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r) (hvec : LL.vec (Fin.last N) = true)
    (hf : f ∈ M.Pol p r LL) (hord : ∀ m ∈ f.support, e ≤ m (Fin.last N, ρ)) (heo : e ≤ LL.deg (Fin.last N)) :
    IsPD LL.total (LL.total + LL.deg (Fin.last N) - e) (fun n => M.tieGam p LL ρ z n f f') := by
  set S := LL.total with hS
  set o := LL.deg (Fin.last N) with ho
  have hoS : o ≤ S := by
    simp only [hS, ho, M.Letters.total]
    exact single_le_sum (f := LL.deg) (fun _ _ => Nat.zero_le _) (mem_univ _)
  obtain ⟨h, hfh, hh⟩ := exists_X_pow_mul (Fin.last N, ρ) e f hord
  have hhP := quot_mem_pol p LL ρ e f h hf hh
  set q := aeval (M.freezeSub p LL ρ) h with hq
  set y := aeval (M.freezeSub p LL ρ) f' with hy
  set w : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c) with hwdef
  set eη : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c) with hedef
  have hw : Function.Injective w := fun a b hab => by simpa [w] using hab
  have he : Function.Injective eη := fun a b hab => by simpa [eη] using hab
  have hwe : ∀ c d, w c ≠ eη d := fun c d h => by
    simp only [w, eη, Prod.mk.injEq] at h; exact (Fin.castSucc_lt_last _).ne h.1
  have hK : ∀ s ∈ q.support, s (eη ρ) ≤ S - e := q_etaDeg p LL ρ e heo h hhP
  have hsub : M.freezeSub p LL ρ (Fin.last N, ρ) = ∑ c, X (w c) * X (eη c) := by
    simp [M.freezeSub, hvec, w, eη]
  have hfreeze : ∀ n, M.freeze p LL ρ n f = (tieE w eη ^ e) (X (eη ρ) ^ (n - S) * q) := by
    intro n
    rw [tieE_pow_apply]
    unfold M.freeze
    rw [hfh, map_mul, map_pow, aeval_X, hsub]
    ring
  have hfreeze' : ∀ n, M.freeze p LL ρ n f' = X (eη ρ) ^ (n - S) * y := fun n => rfl
  have hphi : ∀ n, M.tiePhiAt p (LL.snoc n) (Fin.castSucc (Fin.last N)) (Fin.last (N + 1)) z =
      tiePhi w eη o n z := by
    intro n; simp [M.tiePhiAt, M.Letters.snoc, w, eη, o]
  set T : ℕ → ℕ → ℕ → MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p] := fun j i t =>
    X (w ρ) ^ i * (∑ c, X (w c) * X (eη c)) ^ (e + j - i) *
      (tieF w eη ^ j) (X (eη ρ) ^ (i + t) * (Dp (eη ρ) ^ t) q) with hT
  set Den : ℚ_[p] := ((S.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p]) with hDen
  have key : IsPD S (S + o - e) (fun n => ∑ j ∈ range (o - e + 1),
      ((((o + n + r + z - 1).choose o : ℕ) : ℚ_[p]) *
        (∏ i ∈ range e, (((z : ℚ_[p]) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : ℚ_[p]))) *
          cph ℚ_[p] ((o - e) + (n - e) + r + (z + e) - 1) j) *
        ∑ i ∈ range (e + j + 1), ∑ t ∈ range (S - e + 1),
          (((((n - S).choose i * (n - S - i).choose t : ℕ)) : ℚ_[p]) *
            (((e + j).descFactorial i : ℚ_[p]) / ((i + t).factorial : ℚ_[p]) * (M.fock p y (T j i t) / Den)))) := by
    apply IsPD.sum
    intro j hj
    have hj' : j ≤ o - e := by simpa [Nat.lt_succ_iff] using hj
    refine ((coef_PD o r z e j S hr (by omega) hoS).mul (d' := e + j + (S - e)) ?_).mono (by omega)
    apply IsPD.sum
    intro i hi
    apply IsPD.sum
    intro t ht
    have hi' : i ≤ e + j := by simpa [Nat.lt_succ_iff] using hi
    have ht' : t ≤ S - e := by simpa [Nat.lt_succ_iff] using ht
    exact ((IsPD.choose_prod S i t).mul (IsPD.const S 0 _)).mono (by omega)
  refine key.congr (fun n hn => ?_)
  have hen : e ≤ n := by omega
  have hB := Z_biHom p LL ρ e heo h hhP (n - S)
  rw [show n - S + (LL.total - e) = n - e by omega] at hB
  have hEW := euler_w_of_biHom w eη hB
  have hEH := euler_e_of_biHom w eη hB
  unfold M.tieGam
  rw [hphi n, hfreeze n, hfreeze' n, phi_E_pow hw he hwe e o n z _ heo hen hEW hEH, fock_smul_left, fock_comm,
    fock_expand p he hwe ρ q y (S - e) hK (o - e) (n - e) (z + e) e (n - S)]
  have hm : (((n - S).factorial : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD : Den ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) ?_
    exact prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [show ((((n - S).factorial * S.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p])) =
    (((n - S).factorial : ℕ) : ℚ_[p]) * Den by rw [hDen, Nat.cast_mul]; ring]
  rw [mul_sum, mul_sum, sum_div]
  apply sum_congr rfl
  intro j _
  refine alg_step _ _ _ _ _ _ _ hm hD ?_
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  rw [sum_div]
  apply sum_congr rfl
  intro t _
  simp only [hT]
  ring

end

end Formalism.GM.GammaExpansion

namespace Formalism.GM

open MvPolynomial Finset

theorem gamma_degree_bound : M.GamDeg := by
  intro p _ N r LL ρ z e e' f f' hr hvec hf hf' ho ho'
  have hsym : ∀ n, M.tieGam p LL ρ z n f f' = M.tieGam p LL ρ z n f' f := by
    intro n
    simp only [M.tieGam, M.tiePhiAt]
    rw [GammaExpansion.fock_phi_symm]
  have hle : ∀ (g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (d : ℕ), g ∈ M.Pol p r LL →
      M.HasOrder (Fin.last N, ρ) d g → d ≤ LL.deg (Fin.last N) := by
    intro g d hg hgo
    obtain ⟨_, m, hm, hmd⟩ := hgo
    simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at hg
    have h2 : ∑ c, m (Fin.last N, c) = LL.deg (Fin.last N) := hg hm (Fin.last N)
    rw [← hmd, ← h2]
    exact Finset.single_le_sum (f := fun c => m (Fin.last N, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)
  rcases le_total e' e with h | h
  · obtain ⟨P, hP, hP'⟩ := GammaExpansion.gam_oneSided p N r LL ρ z e f f' hr hvec hf ho.1 (hle f e hf ho)
    exact ⟨P, by rw [max_eq_left h]; exact hP, hP'⟩
  · obtain ⟨P, hP, hP'⟩ := GammaExpansion.gam_oneSided p N r LL ρ z e' f' f hr hvec hf' ho'.1 (hle f' e' hf' ho')
    exact ⟨P, by rw [max_eq_right h]; exact hP, fun n hn => (hsym n).trans (hP' n hn)⟩

end Formalism.GM
