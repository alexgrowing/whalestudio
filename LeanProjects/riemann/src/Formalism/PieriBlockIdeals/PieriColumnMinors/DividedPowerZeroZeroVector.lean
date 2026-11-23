import Formalism.PieriBlockIdeals.StatementLD
import Formalism.GradedWeylDivisibility.FinalD

open MvPolynomial

namespace Formalism.CohomologicalDescent.LD

open Formalism.GradedWeylDivisibility

theorem ld_mu_w (p w i q : ℕ) (lam2 : Fin q → ℕ) : mu p w i lam2 (w : ℤ) = 0 := by
  unfold mu
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun tau htau => ?_
  simp only [shapes, Finset.mem_filter] at htau
  exact htau.2.2.2.2.le

theorem dnNeZero : DnNeZero := by
  intro p w i q lam2
  unfold Dn
  rw [Finset.prod_ne_zero_iff]
  intro k _
  by_cases hk : (w : ℤ) - ((k : ℤ) - (q : ℤ)) = 0
  · have hc : (k : ℤ) - (q : ℤ) = (w : ℤ) := by omega
    rw [hc, ld_mu_w, pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ hk

theorem muSupport : MuSupport := by
  intro p w i q lam2 c hw hmu
  unfold mu at hmu
  obtain ⟨tau, htau, hne⟩ : ∃ tau ∈ shapes p w i lam2, boxesOfContent lam2 tau c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hmu (Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht => (hcon t ht).le))
  unfold boxesOfContent at hne
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at htau
  have h1 := (htau.1 a).2
  have h2 := hw a
  have h3 := a.isLt
  constructor <;> omega

theorem ld_val_split (l : ℕ) (hl : l.Prime) (D : ℤ) (hD : D ≠ 0) :
    ∃ D' : ℤ, D = (l : ℤ) ^ padicValInt l D * D' ∧ ¬ (l : ℤ) ∣ D' := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨D', hD'⟩ := (padicValInt_dvd_iff (p := l) (padicValInt l D) D).mpr (Or.inr le_rfl)
  refine ⟨D', hD', fun hdiv => ?_⟩
  obtain ⟨E, hE⟩ := hdiv
  have h2 : (l : ℤ) ^ (padicValInt l D + 1) ∣ D := ⟨E, by rw [pow_succ, mul_assoc, ← hE]; exact hD'⟩
  rcases (padicValInt_dvd_iff (p := l) (padicValInt l D + 1) D).mp h2 with h3 | h3
  · exact hD h3
  · omega

theorem expLeIffKilled : ExpLeIffKilled := by
  intro l r ν μ e D hl hD
  obtain ⟨D', hD', hnd⟩ := ld_val_split l hl D hD
  set v := padicValInt l D with hv
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  constructor
  · intro h x hx
    obtain ⟨m, hm, hmx⟩ := h x hx
    refine ⟨m, hm, ?_⟩
    have e1 : m * ((l : ℤ) ^ e * D) = D' * (m * (l : ℤ) ^ (e + v)) := by
      rw [hD', pow_add]
      ring
    rw [e1, mul_smul]
    exact Submodule.smul_mem _ _ hmx
  · intro h x hx
    obtain ⟨m, hm, hmx⟩ := h x hx
    refine ⟨m * D', fun hdvd => ?_, ?_⟩
    · rcases hlp.dvd_or_dvd hdvd with h1 | h1
      · exact hm h1
      · exact hnd h1
    · have e1 : m * D' * (l : ℤ) ^ (e + v) = m * ((l : ℤ) ^ e * D) := by
        rw [hD', pow_add]
        ring
      rw [e1]
      exact hmx

theorem expLeMono : ExpLeMono := by
  intro l r ν μ e e' hee h x hx
  obtain ⟨m, hm, hmx⟩ := h x hx
  refine ⟨m, hm, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hee
  have e1 : m * (l : ℤ) ^ (e + d) = (l : ℤ) ^ d * (m * (l : ℤ) ^ e) := by ring
  rw [e1, mul_smul]
  exact Submodule.smul_mem _ _ hmx

theorem expBounded : ExpBounded := by
  intro l r ν hl hν
  obtain ⟨b, ⟨_, hspan, _⟩, _⟩ := sSBasis ℤ r r ν
  have hfin : (ssIdx r r ν).Finite := sSIdxFinite r r ν
  have : Fintype (ssIdx r r ν) := hfin.fintype
  have hb : ∀ m : ssIdx r r ν, ∃ c : ℤ, c ≠ 0 ∧ c • b m ∈ weyl ℤ r r le_rfl ν := by
    intro m
    refine weylRational r r le_rfl ν hν (b m) ?_
    rw [← hspan]
    exact Submodule.subset_span ⟨m, rfl⟩
  choose c hc0 hc using hb
  set Cc : ℤ := ∏ m, c m with hCc
  have hC0 : Cc ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hc0 m
  have hall : ∀ x ∈ dualWeyl ℤ r r ν, Cc • x ∈ weyl ℤ r r le_rfl ν := by
    intro x hx
    rw [← hspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨d, hd⟩ : c m ∣ Cc := Finset.dvd_prod_of_mem c (Finset.mem_univ m)
      rw [hd, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (hc m)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  obtain ⟨D', hD', hnd⟩ := ld_val_split l hl Cc hC0
  refine ⟨padicValInt l Cc, fun μ x hx => ⟨D', hnd, ?_⟩⟩
  have := hall x hx.1
  rwa [hD', mul_comm] at this

theorem plain_implies_one_block : OneRowOfBound := fun h l q w lam2 hl ha hw => h l 1 q w lam2 hl ha hw

theorem gradedImpliesPlain : GradedImpliesPlain := by
  intro h l p q w lam2 hl ha hw eL heL i μ hd
  have h0 : Antitone (0 : Fin (p + q) → ℤ) := fun _ _ _ => le_rfl
  refine h l p q w lam2 0 hl ha hw h0 0 eL (fun μ2 _ => heL μ2) i μ hd ?_
  simp [depth2]

theorem ld_shapes_one (p w y i : ℕ) (hp : 1 ≤ p) (h : y + i ≤ w) :
    shapes p w i (fun _ : Fin 1 => y) = {fun _ => y + i} := by
  ext tau
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨-, -, hsum, -, -⟩
    funext a
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    simpa using hsum
  · rintro rfl
    refine ⟨fun _ => ⟨Nat.le_add_right y i, le_rfl⟩, fun _ _ _ => le_rfl, by simp, ?_, ?_⟩
    · intro b j hj
      unfold colLen
      exact (Finset.card_le_univ _).trans (by simpa using hp)
    · unfold boxesOfContent
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro a - ⟨h1, h2⟩
      push_cast at h2
      omega

theorem ld_mu_one (p w y i : ℕ) (hp : 1 ≤ p) (h : y + i ≤ w) (c : ℤ) :
    mu p w i (fun _ : Fin 1 => y) c = if (y : ℤ) ≤ c ∧ c < (y : ℤ) + (i : ℤ) then 1 else 0 := by
  rw [mu, ld_shapes_one p w y i hp h, Finset.sup_singleton]
  unfold boxesOfContent
  rw [Finset.univ_unique, Finset.filter_singleton]
  have h0 : ((default : Fin 1).val : ℤ) = 0 := by simp
  simp only [h0, add_zero]
  push_cast
  split_ifs <;> simp

theorem dn2 : Dn2 := by
  intro p w y i hp h
  unfold Dn
  have e1 : ∀ k ∈ Finset.range (1 + w + i), ((w : ℤ) - ((k : ℤ) - ((1 : ℕ) : ℤ))) ^
      mu p w i (fun _ : Fin 1 => y) ((k : ℤ) - ((1 : ℕ) : ℤ)) =
      if (y : ℤ) ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 < (y : ℤ) + (i : ℤ) then (w : ℤ) - ((k : ℤ) - 1) else 1 := by
    intro k _
    rw [ld_mu_one p w y i hp h]
    push_cast
    split_ifs <;> simp
  rw [Finset.prod_congr rfl e1, ← Finset.prod_filter]
  have e2 : (Finset.range (1 + w + i)).filter
      (fun k : ℕ => (y : ℤ) ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 < (y : ℤ) + (i : ℤ)) =
      (Finset.range i).image (fun j => j + y + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨k - y - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      push_cast
      omega
  rw [e2, Finset.prod_image (by intro a _ b _ hab; simpa using hab)]
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  push_cast
  omega

noncomputable def ldDet : MvPolynomial (Fin 2 × Fin 2) ℤ := X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)

theorem rank_two_vector_def (w y i : ℕ) : vec2 w y i = X (0, 0) ^ (w - y - i) * X (1, 0) ^ i * ldDet ^ y := rfl

theorem ld_det_ne : ldDet ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => if v.1 = v.2 then (1 : ℤ) else 0)) h
  simp [ldDet] at h'

theorem rank_two_vector_ne_zero (w y i : ℕ) : vec2 w y i ≠ 0 := by
  rw [rank_two_vector_def]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ (X_ne_zero _)))
    (pow_ne_zero _ ld_det_ne)

theorem ld_anti (w y : ℕ) (h : y ≤ w) : Antitone (wt2 w y) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [wt2]

theorem leading_minor_one_eq_entry (h1 : 1 ≤ 2) (h2 : 1 ≤ 2) : lpMinor ℤ (r := 2) (n := 2) 1 h1 h2 = X (0, 0) := by
  unfold lpMinor
  rw [Matrix.det_unique]
  rfl

theorem leading_minor_two_eq_det (h1 : 2 ≤ 2) (h2 : 2 ≤ 2) : lpMinor ℤ (r := 2) (n := 2) 2 h1 h2 = ldDet := by
  unfold lpMinor
  rw [Matrix.det_fin_two]
  rfl

theorem ld_hw (w y : ℕ) : hw ℤ (le_refl 2) (wt2 w y) = vec2 w y 0 := by
  unfold hw
  rw [Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_add, Nat.reduceAdd]
  rw [leading_minor_one_eq_entry, leading_minor_two_eq_det, rank_two_vector_def]
  simp [nuNext, wt2]

theorem rank_two_vector_weighted_homog (w y i : ℕ) (h : y + i ≤ w) :
    IsWeightedHomogeneous (rowW 2 2) (vec2 w y i) (wt2 (w - i) (y + i)) := by
  rw [rank_two_vector_def]
  have hX : ∀ a b : Fin 2, IsWeightedHomogeneous (rowW 2 2)
      (X (a, b) : MvPolynomial (Fin 2 × Fin 2) ℤ) (Pi.single a 1) :=
    fun a b => isWeightedHomogeneous_X _ _ _
  have hD : IsWeightedHomogeneous (rowW 2 2) ldDet (Pi.single 0 1 + Pi.single 1 1) := by
    have h1 := (hX 0 0).mul (hX 1 1)
    have h2 := (hX 0 1).mul (hX 1 0)
    rw [← mem_weightedHomogeneousSubmodule] at h1 h2 ⊢
    exact Submodule.sub_mem _ h1 h2
  have hall := (((hX 0 0).pow (w - y - i)).mul ((hX 1 0).pow i)).mul (hD.pow y)
  convert hall using 1
  funext a
  fin_cases a <;> simp [wt2] <;> omega

theorem ld_rowGen_X (a b : Fin 2) (v : Fin 2 × Fin 2) :
    rowGen ℤ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp only [rowGen, aeval_X]

theorem ld_coeff_lin {S : Type*} [CommRing S] (a b c : S) (m k : ℕ) :
    ((Polynomial.C a + Polynomial.X * Polynomial.C b) ^ m * Polynomial.C c).coeff k =
      (m.choose k : S) * a ^ (m - k) * b ^ k * c := by
  rw [Polynomial.coeff_mul_C]
  congr 1
  rw [add_comm (Polynomial.C a), add_pow, Polynomial.finset_sum_coeff]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      ((Polynomial.X * Polynomial.C b) ^ j * Polynomial.C a ^ (m - j) * (m.choose j : Polynomial S)).coeff k =
        if k = j then (m.choose j : S) * a ^ (m - j) * b ^ j else 0 := by
    intro j _
    rw [show (Polynomial.X * Polynomial.C b) ^ j * Polynomial.C a ^ (m - j) * (m.choose j : Polynomial S) =
        Polynomial.C (b ^ j * a ^ (m - j) * (m.choose j : S)) * Polynomial.X ^ j by
      simp only [mul_pow, map_mul, map_pow, map_natCast]; ring]
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hkj
    · subst hkj; ring
    · rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem ld_coeff_one {S : Type*} [CommRing S] (c : S) (m k : ℕ) :
    ((1 + Polynomial.X) ^ m * Polynomial.C c).coeff k = (m.choose k : S) * c := by
  simpa using ld_coeff_lin (1 : S) 1 c m k

theorem generator_one_zero_det : rowGen ℤ 1 0 ldDet = Polynomial.C ldDet := by
  simp only [ldDet, map_sub, map_mul, ld_rowGen_X]
  norm_num
  ring

theorem generator_zero_one_det : rowGen ℤ 0 1 ldDet = Polynomial.C ldDet := by
  simp only [ldDet, map_sub, map_mul, ld_rowGen_X]
  norm_num
  ring

theorem generator_zero_zero_det : rowGen ℤ 0 0 ldDet = (1 + Polynomial.X) * Polynomial.C ldDet := by
  simp only [ldDet, map_sub, map_mul, ld_rowGen_X]
  norm_num
  ring

theorem generator_one_one_det : rowGen ℤ 1 1 ldDet = (1 + Polynomial.X) * Polynomial.C ldDet := by
  simp only [ldDet, map_sub, map_mul, ld_rowGen_X]
  norm_num
  ring

theorem divided_power_one_zero_vector (w y i k : ℕ) :
    rowDiv ℤ 1 0 k (vec2 w y i) = ((w - y - i).choose k : ℤ) • vec2 w y (i + k) := by
  have h00 : rowGen ℤ 1 0 (X ((0 : Fin 2), (0 : Fin 2))) =
      Polynomial.C (X (0, 0)) + Polynomial.X * Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 1 0 (X ((1 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp
  rw [rowDiv, rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_one_zero_det,
    ← map_pow, ← map_pow, mul_assoc, ← map_mul, ld_coeff_lin, rank_two_vector_def, zsmul_eq_mul,
    Int.cast_natCast, pow_add, show w - y - i - k = w - y - (i + k) by omega]
  ring

theorem divided_power_zero_one_vector (w y i k : ℕ) (h : y + i ≤ w) :
    rowDiv ℤ 0 1 k (vec2 w y i) = (i.choose k : ℤ) • vec2 w y (i - k) := by
  have h00 : rowGen ℤ 0 1 (X ((0 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 0 1 (X ((1 : Fin 2), (0 : Fin 2))) =
      Polynomial.C (X (1, 0)) + Polynomial.X * Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  rw [rowDiv, rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_zero_one_det,
    ← map_pow, ← map_pow, mul_comm (Polynomial.C _), mul_assoc, ← map_mul, ld_coeff_lin, rank_two_vector_def,
    zsmul_eq_mul, Int.cast_natCast]
  rcases Nat.lt_or_ge i k with hki | hki
  · rw [Nat.choose_eq_zero_of_lt hki]
    simp
  · have e1 : w - y - (i - k) = (w - y - i) + k := by omega
    rw [e1, pow_add]
    ring

theorem divided_power_zero_zero_vector (w y i k : ℕ) :
    rowDiv ℤ 0 0 k (vec2 w y i) = ((w - y - i + y).choose k : ℤ) • vec2 w y i := by
  have h00 : rowGen ℤ 0 0 (X ((0 : Fin 2), (0 : Fin 2))) =
      (1 + Polynomial.X) * Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp <;> ring
  have h10 : rowGen ℤ 0 0 (X ((1 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp
  have e : rowGen ℤ 0 0 (vec2 w y i) = (1 + Polynomial.X) ^ (w - y - i + y) * Polynomial.C (vec2 w y i) := by
    rw [rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_zero_zero_det]
    simp only [map_mul, map_pow, mul_pow, pow_add]
    ring
  rw [rowDiv, e, ld_coeff_one, zsmul_eq_mul, Int.cast_natCast]

theorem divided_power_one_one_vector (w y i k : ℕ) :
    rowDiv ℤ 1 1 k (vec2 w y i) = ((i + y).choose k : ℤ) • vec2 w y i := by
  have h00 : rowGen ℤ 1 1 (X ((0 : Fin 2), (0 : Fin 2))) = Polynomial.C (X (0, 0)) := by
    rw [ld_rowGen_X]; simp
  have h10 : rowGen ℤ 1 1 (X ((1 : Fin 2), (0 : Fin 2))) =
      (1 + Polynomial.X) * Polynomial.C (X (1, 0)) := by
    rw [ld_rowGen_X]; simp <;> ring
  have e : rowGen ℤ 1 1 (vec2 w y i) = (1 + Polynomial.X) ^ (i + y) * Polynomial.C (vec2 w y i) := by
    rw [rank_two_vector_def, map_mul, map_mul, map_pow, map_pow, map_pow, h00, h10, generator_one_one_det]
    simp only [map_mul, map_pow, mul_pow, pow_add]
    ring
  rw [rowDiv, e, ld_coeff_one, zsmul_eq_mul, Int.cast_natCast]

theorem rank_two_vector_mem_dual_weyl (w y i : ℕ) (h : y + i ≤ w) : vec2 w y i ∈ dualWeyl ℤ 2 2 (wt2 w y) := by
  have hy : y ≤ w := by omega
  have hhw : vec2 w y 0 ∈ dualWeyl ℤ 2 2 (wt2 w y) := by
    rw [← ld_hw]
    exact hwMem ℤ 2 2 le_rfl (wt2 w y) (ld_anti w y hy)
  have h1 := rowDivStable ℤ 2 2 (wt2 w y) 1 0 i _ hhw
  rw [divided_power_one_zero_vector, zero_add] at h1
  refine dualWeylSat ℤ 2 2 (wt2 w y) _ _ ?_ h1
  have : 0 < (w - y - 0).choose i := Nat.choose_pos (by omega)
  exact_mod_cast this.ne'

theorem ld_minor (s : ℕ) (I : Fin s → Fin 2) (hs : s ≤ 2) :
    (s = 0 ∧ initMinor ℤ I hs = 1) ∨ (s = 1 ∧ ∃ a : Fin 2, initMinor ℤ I hs = X (a, 0)) ∨
      (s = 2 ∧ ∃ ε : ℤ, initMinor ℤ I hs = C ε * ldDet) := by
  obtain rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  · left
    exact ⟨rfl, by unfold initMinor; exact Matrix.det_isEmpty⟩
  · right; left
    refine ⟨rfl, I 0, ?_⟩
    unfold initMinor
    rw [Matrix.det_fin_one]
    rfl
  · right; right
    refine ⟨rfl, ?_⟩
    have h : initMinor ℤ I hs = X (I 0, 0) * X (I 1, 1) - X (I 0, 1) * X (I 1, 0) := by
      unfold initMinor
      rw [Matrix.det_fin_two]
      rfl
    rw [h]
    generalize I 0 = a
    generalize I 1 = b
    have ha : a = 0 ∨ a = 1 := by omega
    have hb : b = 0 ∨ b = 1 := by omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact ⟨0, by rw [C_0]; ring⟩
    · exact ⟨1, by rw [C_1]; unfold ldDet; ring⟩
    · exact ⟨-1, by rw [C_neg, C_1]; unfold ldDet; ring⟩
    · exact ⟨0, by rw [C_0]; ring⟩

theorem ld_prod {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∃ (ε : ℤ) (α β : ℕ), ∏ k ∈ S, initMinor ℤ (I k) (hsz k) =
        C ε * (X (0, 0) ^ α * X (1, 0) ^ β * ldDet ^ (S.filter fun k => 1 < sz k).card) ∧
      α + β + (S.filter fun k => 1 < sz k).card = (S.filter fun k => 0 < sz k).card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 0, 0, by simp, by simp⟩
  | insert k S hk ih =>
    obtain ⟨ε, α, β, hprod, hcard⟩ := ih
    have hk1 : k ∉ S.filter fun k => 1 < sz k := fun h => hk (Finset.mem_filter.mp h).1
    have hk0 : k ∉ S.filter fun k => 0 < sz k := fun h => hk (Finset.mem_filter.mp h).1
    rw [Finset.prod_insert hk, hprod, Finset.filter_insert, Finset.filter_insert]
    rcases ld_minor (sz k) (I k) (hsz k) with ⟨h0, hm⟩ | ⟨h1, a, hm⟩ | ⟨h2, ε', hm⟩
    · rw [hm, if_neg (by omega), if_neg (by omega)]
      exact ⟨ε, α, β, by ring, hcard⟩
    · rw [hm, if_neg (by omega), if_pos (by omega), Finset.card_insert_of_notMem hk0]
      have ha : a = 0 ∨ a = 1 := by omega
      rcases ha with rfl | rfl
      · exact ⟨ε, α + 1, β, by ring, by omega⟩
      · exact ⟨ε, α, β + 1, by ring, by omega⟩
    · rw [hm, if_pos (by omega), if_pos (by omega), Finset.card_insert_of_notMem hk0,
        Finset.card_insert_of_notMem hk1]
      exact ⟨ε' * ε, α, β, by rw [C_mul]; ring, by omega⟩

theorem ld_nabla_le (w y : ℕ) (hy : y ≤ w) :
    dualWeyl ℤ 2 2 (wt2 w y) ≤ Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = vec2 w y j} := by
  rw [standardMonomialSpan 2 2 (wt2 w y) (ld_anti w y hy)]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hshape, rfl⟩
  obtain ⟨ε, α, β, hprod, hcard⟩ := ld_prod sz hsz I Finset.univ
  have h0 : (Finset.univ.filter fun k => 0 < sz k).card = w := congrFun hshape 0
  have h1 : (Finset.univ.filter fun k => 1 < sz k).card = y := congrFun hshape 1
  rw [h0, h1] at hcard
  rw [h1] at hprod
  have hα : α = w - y - β := by omega
  have : bideterminant ℤ sz hsz I = ε • vec2 w y β := by
    unfold bideterminant
    rw [hprod, hα, ← rank_two_vector_def, smul_eq_C_mul]
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, by omega, rfl⟩)

theorem ld_nablaWt_le (w y : ℕ) (hy : y ≤ w) (μ : Fin 2 → ℕ)
    (T : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ))
    (hT : ∀ j, y + j ≤ w → wt2 (w - j) (y + j) = μ → vec2 w y j ∈ T) :
    nablaWt 2 (wt2 w y) μ ≤ T := by
  intro x hx
  have hx1 := ld_nabla_le w y hy hx.1
  have hx2 : IsWeightedHomogeneous (rowW 2 2) x μ := hx.2
  rw [← hx2.weightedHomogeneousComponent_same]
  have hmap : Submodule.map (weightedHomogeneousComponent (R := ℤ) (rowW 2 2) μ)
      (Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = vec2 w y j}) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    by_cases hμ : wt2 (w - j) (y + j) = μ
    · subst hμ
      rw [SetLike.mem_coe, (rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_same]
      exact hT j hj rfl
    · rw [SetLike.mem_coe, (rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_ne μ (Ne.symm hμ)]
      exact T.zero_mem
  exact hmap (Submodule.mem_map_of_mem hx1)

theorem rank2Other : Rank2Other := by
  intro w y μ hy h
  refine le_bot_iff.mp (ld_nablaWt_le w y hy μ ⊥ ?_)
  intro j hj hμ
  exact absurd hμ.symm (h j hj)

noncomputable def ldM (w y : ℕ) : Submodule ℤ (MvPolynomial (Fin 2 × Fin 2) ℤ) :=
  Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = ((w - y).choose j : ℤ) • vec2 w y j}

theorem ld_M_gen (w y j : ℕ) (hj : y + j ≤ w) : ((w - y).choose j : ℤ) • vec2 w y j ∈ ldM w y := Submodule.subset_span ⟨j, hj, rfl⟩

theorem ld_M_stable (w y : ℕ) (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) ℤ)
    (hf : f ∈ ldM w y) : rowDiv ℤ a b k f ∈ ldM w y := by
  unfold ldM at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    rw [rowDiv_smul]
    have ha : a = 0 ∨ a = 1 := by omega
    have hb : b = 0 ∨ b = 1 := by omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [divided_power_zero_zero_vector, smul_comm]
      exact Submodule.smul_mem _ _ (ld_M_gen w y j hj)
    · rw [divided_power_zero_one_vector w y j k hj]
      by_cases hk : k ≤ j
      · have hid : (w - y).choose j * j.choose k = (w - y - (j - k)).choose k * (w - y).choose (j - k) := by
          have h1 := Nat.choose_mul (n := w - y) (k := j) (s := j - k) (Nat.sub_le j k)
          rw [Nat.choose_symm hk, Nat.sub_sub_self hk] at h1
          rw [h1, mul_comm]
        rw [smul_smul]
        have hid' : (((w - y).choose j : ℕ) : ℤ) * ((j.choose k : ℕ) : ℤ) =
            (((w - y - (j - k)).choose k : ℕ) : ℤ) * (((w - y).choose (j - k) : ℕ) : ℤ) := by
          exact_mod_cast hid
        rw [hid', ← smul_smul]
        exact Submodule.smul_mem _ _ (ld_M_gen w y (j - k) (by omega))
      · rw [Nat.choose_eq_zero_of_lt (show j < k by omega)]
        simp
    · rw [divided_power_one_zero_vector]
      by_cases hk : y + (j + k) ≤ w
      · have hid : (w - y).choose j * (w - y - j).choose k = (j + k).choose j * (w - y).choose (j + k) := by
          have h1 := Nat.choose_mul (n := w - y) (k := j + k) (s := j) (Nat.le_add_right j k)
          rw [Nat.add_sub_cancel_left] at h1
          rw [← h1, mul_comm]
        rw [smul_smul]
        have hid' : (((w - y).choose j : ℕ) : ℤ) * (((w - y - j).choose k : ℕ) : ℤ) =
            (((j + k).choose j : ℕ) : ℤ) * (((w - y).choose (j + k) : ℕ) : ℤ) := by
          exact_mod_cast hid
        rw [hid', ← smul_smul]
        exact Submodule.smul_mem _ _ (ld_M_gen w y (j + k) hk)
      · rw [Nat.choose_eq_zero_of_lt (show w - y - j < k by omega)]
        simp
    · rw [divided_power_one_one_vector, smul_comm]
      exact Submodule.smul_mem _ _ (ld_M_gen w y j hj)
  | zero =>
    have : rowDiv ℤ a b k (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) = 0 := (rowDivL ℤ a b k).map_zero
    rw [this]
    exact Submodule.zero_mem _
  | add x z _ _ hx hz =>
    rw [rowDiv_add]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [rowDiv_smul]
    exact Submodule.smul_mem _ _ hx

theorem ld_weyl_le (w y : ℕ) (hy : y ≤ w) : weyl ℤ 2 2 le_rfl (wt2 w y) ≤ ldM w y := by
  unfold weyl
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨wd, rfl⟩
  show applyWord ℤ wd (hw ℤ le_rfl (wt2 w y)) ∈ ldM w y
  induction wd with
  | nil =>
    show hw ℤ le_rfl (wt2 w y) ∈ ldM w y
    rw [ld_hw]
    have := ld_M_gen w y 0 (by omega)
    simpa using this
  | cons x wd ih =>
    rw [applyWord_cons]
    exact ld_M_stable w y _ _ _ _ ih

theorem ld_gen_mem_weyl (w y j : ℕ) :
    ((w - y).choose j : ℤ) • vec2 w y j ∈ weyl ℤ 2 2 le_rfl (wt2 w y) := by
  have h0 : hw ℤ le_rfl (wt2 w y) ∈ weyl ℤ 2 2 le_rfl (wt2 w y) :=
    Submodule.subset_span ⟨[], rfl⟩
  have h1 := weylRowDivStable ℤ 2 2 le_rfl (wt2 w y) 1 0 j _ h0
  rw [ld_hw, divided_power_one_zero_vector, zero_add] at h1
  exact h1

theorem rank2Exact : Rank2Exact := by
  intro w y i h
  have hy : y ≤ w := by omega
  refine ⟨le_antisymm ?_ ?_, rank_two_vector_ne_zero w y i, ?_⟩
  · refine ld_nablaWt_le w y hy _ _ ?_
    intro j hj hμ
    have h1 : y + j = y + i := congrFun hμ 1
    have hji : j = i := by omega
    rw [hji]
    exact Submodule.mem_span_singleton_self _
  · refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    exact ⟨rank_two_vector_mem_dual_weyl w y i h, rank_two_vector_weighted_homog w y i h⟩
  · intro c
    constructor
    · intro hc
      have hcM := ld_weyl_le w y hy hc
      have hmap : Submodule.map (weightedHomogeneousComponent (R := ℤ) (rowW 2 2) (wt2 (w - i) (y + i)))
          (ldM w y) ≤ Submodule.span ℤ {((w - y).choose i : ℤ) • vec2 w y i} := by
        unfold ldM
        rw [Submodule.map_span]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        rw [SetLike.mem_coe, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [(rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_same]
          exact Submodule.mem_span_singleton_self _
        · have hne : wt2 (w - i) (y + i) ≠ wt2 (w - j) (y + j) := by
            intro hμ
            have h1 : y + i = y + j := congrFun hμ 1
            omega
          rw [(rank_two_vector_weighted_homog w y j hj).weightedHomogeneousComponent_ne _ hne, smul_zero]
          exact Submodule.zero_mem _
      have h2 := hmap (Submodule.mem_map_of_mem hcM)
      rw [map_smul, (rank_two_vector_weighted_homog w y i h).weightedHomogeneousComponent_same] at h2
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp h2
      rw [smul_smul] at hd
      have h3 : (d * ((w - y).choose i : ℤ) - c) • vec2 w y i = 0 := by
        rw [sub_smul, hd, sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact ⟨d, by linarith⟩
      · exact absurd h4 (rank_two_vector_ne_zero w y i)
    · rintro ⟨d, rfl⟩
      rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (ld_gen_mem_weyl w y i)

theorem ld_rank2_core (l w y : ℕ) (hl : l.Prime) (hy : y ≤ w) (e i : ℕ) (μ : Fin 2 → ℕ)
    (hd : μ 0 + i = w) :
    ExpLe l 2 (wt2 w y) μ (e + padicValInt l (Dn 1 w i (fun _ : Fin 1 => y))) := by
  rw [expLeIffKilled l 2 _ μ e _ hl (dnNeZero 1 w i 1 _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hex : ∃ j, y + j ≤ w ∧ μ = wt2 (w - j) (y + j)
  · obtain ⟨j, hj, rfl⟩ := hex
    have hd' : w - j + i = w := hd
    have hij : j = i := by omega
    subst hij
    rw [(rank2Exact w y j hj).1] at hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [dn2 1 w y j le_rfl hj, smul_smul]
    have : (1 * ((l : ℤ) ^ e * ((j.factorial * (w - y).choose j : ℕ) : ℤ)) * c) =
        ((l : ℤ) ^ e * (j.factorial : ℤ) * c) * ((w - y).choose j : ℤ) := by
      push_cast
      ring
    rw [this, mul_smul]
    exact Submodule.smul_mem _ _ (ld_gen_mem_weyl w y j)
  · have hbot := rank2Other w y μ hy (fun j hj hμ => hex ⟨j, hj, hμ⟩)
    rw [hbot] at hx
    rw [(Submodule.mem_bot ℤ).mp hx, smul_zero]
    exact Submodule.zero_mem _

theorem ld_blockWt2 (w y : ℕ) : blockWt 1 1 w (fun _ : Fin 1 => y) = wt2 w y := by
  funext a
  fin_cases a <;> rfl

theorem lemmaD_rank2 : LemmaD_rank2 := by
  intro l w y hl hy eL _ i μ hd
  have hd' : μ 0 + i = w := by simpa [IsDepth] using hd
  rw [ld_blockWt2]
  exact ld_rank2_core l w y hl hy eL i μ hd'

theorem lemmaDGraded_rank2 : LemmaDGraded_rank2 := by
  intro l w y ξ hl hy _ i' eL _ i μ hd _
  have hd' : μ 0 + i = w := by simpa [IsDepth] using hd
  rw [ld_blockWt2]
  exact ld_rank2_core l w y hl hy eL i μ hd'

theorem ld_boxes_le (p w i q : ℕ) (lam2 tau : Fin q → ℕ) (htau : tau ∈ shapes p w i lam2) (c : ℤ) :
    boxesOfContent lam2 tau c ≤ p := by
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset] at htau
  obtain ⟨-, hanti, -, hcol, -⟩ := htau
  unfold boxesOfContent
  rcases (Finset.univ.filter fun a : Fin q =>
      (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp
  · have hb := Finset.max'_mem _ hS
    have hb' := (Finset.mem_filter.mp hb).2
    have hj0 : 0 ≤ c + (((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS).val : ℤ) :=
      le_trans (Int.natCast_nonneg _) hb'.1
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hj0
    have hjt : j < tau ((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS) := by omega
    refine le_trans (Finset.card_le_card ?_) (hcol _ j hjt)
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    have hab := Finset.le_max' _ a ha
    have hab' : (a.val : ℤ) ≤ (((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS).val : ℤ) := by
      exact_mod_cast hab
    have htb := hanti a _ hab
    simp only [colLen, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> omega

theorem muLe : MuLe := by
  intro p w i q lam2 c
  unfold mu
  exact Finset.sup_le fun tau h => ld_boxes_le p w i q lam2 tau h c

theorem muRange : MuRange := by
  intro p w i q m lam2 c hlam hmu
  unfold mu at hmu
  obtain ⟨tau, htau, hne⟩ : ∃ tau ∈ shapes p w i lam2, boxesOfContent lam2 tau c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hmu (Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht => (hcon t ht).le))
  unfold boxesOfContent at hne
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [shapes, Finset.mem_filter] at htau
  have hz := htau.2.2.2.2
  unfold boxesOfContent at hz
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz
  have hna := hz (Finset.mem_univ a)
  have h1 := hlam a
  have h3 := a.isLt
  constructor
  · omega
  · by_contra hc
    push_neg at hc
    exact hna ⟨by omega, by omega⟩

theorem dnPos : DnPos := by
  intro p w i q lam2 hw
  unfold Dn
  refine Finset.prod_pos fun k _ => ?_
  by_cases hmu : mu p w i lam2 ((k : ℤ) - (q : ℤ)) = 0
  · rw [hmu, pow_zero]
    exact one_pos
  · have hlt := (muRange p w i q 0 lam2 _ (fun b => ⟨Nat.zero_le _, hw b⟩) hmu).2
    exact pow_pos (by omega) _

theorem dnDvd : DnDvd := by
  intro p w i q m lam2 hb
  unfold Dn
  have hfac : ∀ k ∈ Finset.range (q + w + i),
      ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ)) ∣
        (((if k ∈ Finset.Ico (m + 1) (w + q) then (w + q - k) ^ p else 1 : ℕ)) : ℤ) := by
    intro k _
    by_cases hmu : mu p w i lam2 ((k : ℤ) - (q : ℤ)) = 0
    · rw [hmu, pow_zero]
      exact one_dvd _
    · have h := muRange p w i q m lam2 _ hb hmu
      have hk : k ∈ Finset.Ico (m + 1) (w + q) := Finset.mem_Ico.mpr (by omega)
      rw [if_pos hk]
      have he : ((w : ℤ) - ((k : ℤ) - (q : ℤ))) = ((w + q - k : ℕ) : ℤ) := by omega
      rw [he, Nat.cast_pow]
      exact pow_dvd_pow _ (muLe p w i q lam2 _)
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ hfac) ?_
  rw [← Nat.cast_prod, Finset.prod_ite_mem]
  have hsub : Finset.range (q + w + i) ∩ Finset.Ico (m + 1) (w + q) = Finset.Ico (m + 1) (w + q) := by
    refine Finset.inter_eq_right.mpr ?_
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  rw [hsub, Finset.prod_pow, Finset.prod_Ico_eq_prod_range]
  have hH : w + q - (m + 1) = w + q - m - 1 := by omega
  have hprod : ∏ j ∈ Finset.range (w + q - (m + 1)), (w + q - (m + 1 + j)) = (w + q - m - 1).factorial := by
    rw [hH, ← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range]
    refine Finset.prod_congr rfl ?_
    intro j _
    omega
  rw [hprod]

theorem dnVal : DnVal := by
  intro l p w i q m lam2 hl hb
  have : Fact l.Prime := ⟨hl⟩
  have hdvd := dnDvd p w i q m lam2 hb
  have h1 : (l : ℤ) ^ padicValInt l (Dn p w i lam2) ∣ (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) :=
    dvd_trans (padicValInt_dvd _) hdvd
  have hF : (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero p (Nat.factorial_ne_zero _)
  have h2 : padicValInt l (Dn p w i lam2) ≤ padicValInt l (((w + q - m - 1).factorial ^ p : ℕ) : ℤ) := by
    rcases (padicValInt_dvd_iff _ _).mp h1 with h | h
    · exact absurd h hF
    · exact h
  rw [padicValInt.of_nat, padicValNat.pow] at h2
  have h3 := sub_one_mul_padicValNat_factorial (p := l) (w + q - m - 1)
  calc (l - 1) * padicValInt l (Dn p w i lam2)
      ≤ (l - 1) * (p * padicValNat l (w + q - m - 1).factorial) := Nat.mul_le_mul_left _ h2
    _ = p * ((l - 1) * padicValNat l (w + q - m - 1).factorial) := by ring
    _ ≤ p * (w + q - m - 1) := Nat.mul_le_mul_left _ (by rw [h3]; exact Nat.sub_le _ _)

theorem ld_blockWt_anti (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w) :
    Antitone (blockWt p q w lam2) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp only [blockWt, Fin.append_left, le_refl]
    | right j =>
      simp only [blockWt, Fin.append_left, Fin.append_right]
      exact hb j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      have := j.isLt
      rw [Fin.le_def] at hij
      simp at hij
      omega
    | right j =>
      simp only [blockWt, Fin.append_right]
      apply ha
      rw [Fin.le_def] at hij ⊢
      simpa using hij

theorem peelBound : PeelBound := by
  intro hD l q w m lam2 hl ha hb eL heL μ
  have hbw : ∀ b, lam2 b ≤ w := fun b => (hb b).2
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  by_cases hμ : μ (Fin.castAdd q (0 : Fin 1)) ≤ w
  · have hd : IsDepth 1 q w μ (w - μ (Fin.castAdd q (0 : Fin 1))) := by
      simp only [IsDepth, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul]
      omega
    have h1 := hD l q w lam2 hl ha hbw eL heL _ μ hd
    refine expLeMono l _ _ μ _ _ ?_ h1
    refine Nat.add_le_add_left ?_ eL
    refine (Nat.le_div_iff_mul_le hl1).mpr ?_
    have h2 := dnVal l 1 w (w - μ (Fin.castAdd q (0 : Fin 1))) q m lam2 hl hb
    rw [one_mul] at h2
    rw [mul_comm]
    exact h2
  · intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
      have hdom := (dualWeylDominanceZ (1 + q) (1 + q) (blockWt 1 q w lam2) le_rfl
        (ld_blockWt_anti 1 q w lam2 ha hbw) x hx.1 d hd).1 1
      have hf : (Finset.univ.filter fun a : Fin (1 + q) => a.val < 1) = {Fin.castAdd q (0 : Fin 1)} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
          Fin.val_castAdd, Fin.val_zero]
        omega
      rw [hf, Finset.sum_singleton, Finset.sum_singleton] at hdom
      have hwt : Finsupp.weight (rowW (1 + q) (1 + q)) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
      rw [← ldrow_weight_rowW, hwt] at hdom
      have hnu : rowNu (r := 1 + q) (blockWt 1 q w lam2) (Fin.castAdd q (0 : Fin 1)) = w := by
        unfold rowNu
        rw [dif_pos (Fin.castAdd q (0 : Fin 1)).isLt]
        exact Fin.append_left _ _ 0
      rw [hnu] at hdom
      exact hμ hdom
    refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [hx0, smul_zero]
    exact Submodule.zero_mem _

def ldZ (q : ℕ) : Fin (1 + q) := Fin.castAdd q (0 : Fin 1)

theorem symmetric_block_weight_zero (q w : ℕ) : blockWt 1 q w (fun _ => 0) (ldZ q) = w := by
  simp only [blockWt, ldZ, Fin.append_left]

theorem ld_sym_nu_ne (q w : ℕ) (s : Fin (1 + q)) (hs : s ≠ ldZ q) : blockWt 1 q w (fun _ => 0) s = 0 := by
  induction s using Fin.addCases with
  | left i =>
    exfalso
    apply hs
    simp only [ldZ]
    congr 1
    exact Subsingleton.elim _ _
  | right j => simp only [blockWt, Fin.append_right]

theorem ld_sym_hw (q w : ℕ) :
    hw ℤ (le_refl (1 + q)) (blockWt 1 q w (fun _ => 0)) = X (ldZ q, ldZ q) ^ w := by
  unfold hw
  rw [Finset.prod_eq_single (ldZ q)]
  · have h1 : nuNext (blockWt 1 q w fun _ => 0) (ldZ q) = 0 := by
      unfold nuNext
      split_ifs with h
      · apply ld_sym_nu_ne
        intro heq
        exact absurd (congrArg Fin.val heq) (by simp)
      · rfl
    rw [h1, symmetric_block_weight_zero, Nat.sub_zero]
    congr 1
    have hz : ((ldZ q : Fin (1 + q)) : ℕ) = 0 := rfl
    simp only [hz, zero_add]
    unfold lpMinor
    rw [Matrix.det_unique]
    rfl
  · intro b _ hb
    rw [ld_sym_nu_ne q w b hb, Nat.zero_sub, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

noncomputable def ldSv (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) :
    MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ :=
  X (ldZ q, ldZ q) ^ (w - ∑ a ∈ S, μ a) * ∏ a ∈ S, X (a, ldZ q) ^ μ a

theorem ld_sym_rowGen (q : ℕ) (a b : Fin (1 + q)) (v : Fin (1 + q) × Fin (1 + q)) :
    rowGen ℤ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp only [rowGen, aeval_X]

theorem ld_sym_step (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (a : Fin (1 + q))
    (ha : a ∉ S) (hz : ldZ q ∉ S) :
    rowDiv ℤ a (ldZ q) (μ a) (ldSv q w μ S) =
      ((w - ∑ b ∈ S, μ b).choose (μ a) : ℤ) • ldSv q w μ (insert a S) := by
  have hg : rowGen ℤ a (ldZ q) (ldSv q w μ S) =
      (Polynomial.C (X (ldZ q, ldZ q)) + Polynomial.X * Polynomial.C (X (a, ldZ q))) ^ (w - ∑ b ∈ S, μ b) *
        Polynomial.C (∏ b ∈ S, X (b, ldZ q) ^ μ b) := by
    unfold ldSv
    rw [map_mul, map_pow, ld_sym_rowGen, if_pos rfl, map_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    have hbz : ¬ (b, ldZ q).1 = ldZ q := fun h => hz (h ▸ hb)
    rw [map_pow, ld_sym_rowGen, if_neg hbz, add_zero, map_pow]
  unfold rowDiv
  rw [hg, ld_coeff_lin]
  unfold ldSv
  rw [Finset.sum_insert ha, Finset.prod_insert ha, zsmul_eq_mul, add_comm (μ a), Nat.sub_add_eq]
  push_cast
  ring

theorem ld_sym_mem (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (hz : ldZ q ∉ S)
    (hS : ∑ a ∈ S, μ a ≤ w) :
    ∃ c : ℕ, c ∣ w.descFactorial (∑ a ∈ S, μ a) ∧
      (c : ℤ) • ldSv q w μ S ∈ weyl ℤ (1 + q) (1 + q) le_rfl (blockWt 1 q w fun _ => 0) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp, ?_⟩
    have h0 : ldSv q w μ ∅ = hw ℤ (le_refl (1 + q)) (blockWt 1 q w (fun _ => 0)) := by
      rw [ld_sym_hw]
      simp [ldSv]
    rw [h0, Nat.cast_one, one_smul]
    exact Submodule.subset_span ⟨[], rfl⟩
  | insert a S ha ih =>
    have hz' : ldZ q ∉ S := fun h => hz (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert ha] at hS
    obtain ⟨c, hc, hmem⟩ := ih hz' (by omega)
    refine ⟨c * (w - ∑ b ∈ S, μ b).choose (μ a), ?_, ?_⟩
    · rw [Finset.sum_insert ha, add_comm (μ a)]
      have h1 := Nat.descFactorial_mul_descFactorial (n := w) (k := ∑ b ∈ S, μ b)
        (m := ∑ b ∈ S, μ b + μ a) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h1
      rw [← h1, mul_comm]
      refine Nat.mul_dvd_mul ?_ hc
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.intro_left _ rfl
    · have h2 := weylRowDivStable ℤ (1 + q) (1 + q) le_rfl (blockWt 1 q w fun _ => 0) a (ldZ q) (μ a) _ hmem
      rw [rowDiv_smul, ld_sym_step q w μ S a ha hz', smul_smul] at h2
      push_cast
      exact h2

theorem ld_sym_unique (q w : ℕ) (μ : Fin (1 + q) → ℕ) (x : MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ)
    (hx : x ∈ nablaWt (1 + q) (blockWt 1 q w fun _ => 0) μ) (hne : x ≠ 0) :
    ∑ a, μ a = w ∧ ∃ c : ℤ, x = c • ∏ a, X (a, ldZ q) ^ μ a := by
  have key : ∀ d ∈ x.support, d = ∑ a, Finsupp.single (a, ldZ q) (μ a) ∧ ∑ a, μ a = w := by
    intro d hd
    have hd' := MvPolynomial.mem_support_iff.mp hd
    have hcolw : Finsupp.weight (colW (1 + q) (1 + q)) d = blockWt 1 q w fun _ => 0 := hx.1.1 hd'
    have hroww : Finsupp.weight (rowW (1 + q) (1 + q)) d = μ := hx.2 hd'
    have hcol : ∀ s, ∑ a, d (a, s) = blockWt 1 q w (fun _ => 0) s := fun s => by
      rw [← lccomp_weight_colW_apply, hcolw]
    have hrow : ∀ a, rowDeg d a = μ a := fun a => by
      rw [← ldrow_weight_rowW, hroww]
    have hzero : ∀ a s, s ≠ ldZ q → d (a, s) = 0 := by
      intro a s hs
      have h1 := hcol s
      rw [ld_sym_nu_ne q w s hs] at h1
      exact (Finset.sum_eq_zero_iff.mp h1) a (Finset.mem_univ a)
    have hdz : ∀ a, d (a, ldZ q) = μ a := by
      intro a
      rw [← hrow a]
      unfold rowDeg
      exact (Finset.sum_eq_single (ldZ q) (fun s _ hs => hzero a s hs)
        (fun h => absurd (Finset.mem_univ _) h)).symm
    constructor
    · ext ⟨a, s⟩
      rw [Finsupp.finsetSum_apply]
      by_cases hs : s = ldZ q
      · subst hs
        rw [Finset.sum_eq_single a]
        · rw [Finsupp.single_eq_same, hdz]
        · intro b _ hb
          exact Finsupp.single_eq_of_ne (by intro h; exact hb (Prod.mk.inj h).1.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [hzero a s hs]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        exact Finsupp.single_eq_of_ne (by intro h; exact hs (Prod.mk.inj h).2)
    · have h1 := hcol (ldZ q)
      rw [symmetric_block_weight_zero] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun a _ => (hdz a).symm
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
  refine ⟨(key d hd).2, coeff (∑ a, Finsupp.single (a, ldZ q) (μ a)) x, ?_⟩
  have hprod : ∏ a, (X (a, ldZ q) : MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ) ^ μ a =
      monomial (∑ a, Finsupp.single (a, ldZ q) (μ a)) 1 := by
    rw [monomial_sum_one]
    exact Finset.prod_congr rfl fun a _ => X_pow_eq_monomial
  rw [hprod]
  ext d'
  rw [coeff_smul, coeff_monomial]
  by_cases hd' : ∑ a, Finsupp.single (a, ldZ q) (μ a) = d'
  · rw [if_pos hd', hd', smul_eq_mul, mul_one]
  · rw [if_neg hd', smul_zero]
    by_contra hc
    exact hd' (key d' (MvPolynomial.mem_support_iff.mpr hc)).1.symm

theorem ld_sym_shape (q w i : ℕ) (hi : i ≤ w) :
    (fun a : Fin q => if a.val = 0 then i else 0) ∈ shapes 1 w i (fun _ : Fin q => 0) ∨ q = 0 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · exact Or.inr hq
  left
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun a => ⟨Nat.zero_le _, by split_ifs <;> omega⟩, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : a.val ≤ b.val := hab
    split_ifs <;> omega
  · simp [Fin.sum_univ_succ]
  · intro b j hj
    unfold colLen
    rw [Finset.card_le_one]
    intro a ha c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hc
    apply Fin.ext
    split_ifs at ha hc <;> omega
  · unfold boxesOfContent
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a - ⟨-, h2⟩
    beta_reduce at h2
    split_ifs at h2 <;> omega

theorem ld_sym_mu (q w i : ℕ) (hq : 0 < q) (hi : i ≤ w) (c : ℤ) (h0 : 0 ≤ c) (h1 : c < (i : ℤ)) :
    mu 1 w i (fun _ : Fin q => 0) c ≠ 0 := by
  have hmem := (ld_sym_shape q w i hi).resolve_right (by omega)
  intro h0'
  have hle := Finset.le_sup (f := fun tau => boxesOfContent (fun _ : Fin q => 0) tau c) hmem
  unfold mu at h0'
  rw [h0'] at hle
  have hpos : 0 < boxesOfContent (fun _ : Fin q => 0) (fun a : Fin q => if a.val = 0 then i else 0) c := by
    unfold boxesOfContent
    apply Finset.card_pos.mpr
    refine ⟨⟨0, hq⟩, ?_⟩
    simp
    omega
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

theorem ld_sym_Dn (q w i : ℕ) (hq : 0 < q) (hi : i ≤ w) :
    ((w.descFactorial i : ℕ) : ℤ) ∣ Dn 1 w i (fun _ : Fin q => 0) := by
  unfold Dn
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hsub : (Finset.range i).image (fun c => c + q) ⊆ Finset.range (q + w + i) := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  rw [Finset.prod_image (by intro a _ b _ hab; simpa using hab)]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun c hc => ?_
  rw [Finset.mem_range] at hc
  have e : ((c + q : ℕ) : ℤ) - (q : ℤ) = (c : ℤ) := by push_cast; ring
  simp only [e]
  have hmu := ld_sym_mu q w i hq hi (c : ℤ) (by positivity) (by exact_mod_cast hc)
  have hc' : ((w - c : ℕ) : ℤ) = (w : ℤ) - (c : ℤ) := by rw [Nat.cast_sub (by omega)]
  rw [hc']
  exact dvd_pow_self _ hmu

theorem lemmaD_sym : LemmaD_sym := by
  intro l q w hl eL _ i μ hd
  rw [expLeIffKilled l _ _ μ eL _ hl (dnNeZero 1 w i q _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hne : x = 0
  · rw [hne, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨hsum, c, rfl⟩ := ld_sym_unique q w μ x hx hne
  have hd' : μ (ldZ q) + i = w := by
    have := hd
    simp only [IsDepth, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul] at this
    exact this
  have hsplit : μ (ldZ q) + ∑ a ∈ Finset.univ.erase (ldZ q), μ a = w := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    exact hsum
  have hSi : ∑ a ∈ Finset.univ.erase (ldZ q), μ a = i := by omega
  obtain ⟨c', hc', hmem⟩ := ld_sym_mem q w μ (Finset.univ.erase (ldZ q)) (Finset.notMem_erase _ _) (by omega)
  have hv : ldSv q w μ (Finset.univ.erase (ldZ q)) = ∏ a, X (a, ldZ q) ^ μ a := by
    unfold ldSv
    rw [hSi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (ldZ q))]
    have : w - i = μ (ldZ q) := by omega
    rw [this]
  rw [hv] at hmem
  rw [hSi] at hc'
  have hdvd : ((c' : ℕ) : ℤ) ∣ Dn 1 w i (fun _ : Fin q => 0) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      have hi0 : i = 0 := by
        rw [← hSi]
        refine Finset.sum_eq_zero fun a ha => ?_
        have hlt := a.isLt
        exact absurd (Fin.ext (show a.val = (ldZ 0).val from by have h0 : (ldZ 0).val = 0 := rfl; omega)) (Finset.ne_of_mem_erase ha)
      subst hi0
      have : c' = 1 := by simpa using hc'
      rw [this]
      simp
    · exact dvd_trans (Int.natCast_dvd_natCast.mpr hc') (ld_sym_Dn q w i hq (by omega))
  obtain ⟨e, he⟩ := hdvd
  rw [smul_smul, he]
  have : (1 * ((l : ℤ) ^ eL * ((c' : ℤ) * e)) * c) = ((l : ℤ) ^ eL * e * c) * (c' : ℤ) := by ring
  rw [this, mul_smul]
  exact Submodule.smul_mem _ _ hmem

theorem d_n_ne_zero : DnNeZero := dnNeZero
theorem mu_support : MuSupport := muSupport
theorem exponent_le_iff_killed : ExpLeIffKilled := expLeIffKilled
theorem exponent_le_monotone : ExpLeMono := expLeMono
theorem exponent_bounded : ExpBounded := expBounded
theorem graded_implies_plain : GradedImpliesPlain := gradedImpliesPlain
theorem plain_implies_one_block_thm : OneRowOfBound := plain_implies_one_block
theorem d_n_rank_two : Dn2 := dn2
theorem rank_two_exact_case : Rank2Exact := rank2Exact
theorem rank_two_other_case : Rank2Other := rank2Other
theorem lemma_d_rank_two : LemmaD_rank2 := lemmaD_rank2
theorem lemma_d_graded_rank_two : LemmaDGraded_rank2 := lemmaDGraded_rank2
theorem mu_le_alt : MuLe := muLe
theorem mu_range : MuRange := muRange
theorem d_n_pos : DnPos := dnPos
theorem d_n_dvd : DnDvd := dnDvd
theorem d_n_value : DnVal := dnVal
theorem peel_bound : PeelBound := peelBound
theorem lemma_d_symmetric : LemmaD_sym := lemmaD_sym

end Formalism.CohomologicalDescent.LD
