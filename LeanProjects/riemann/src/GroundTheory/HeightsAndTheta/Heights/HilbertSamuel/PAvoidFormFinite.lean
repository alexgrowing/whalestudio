import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAvoidFormFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace AvoidFormFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem bdeg_add (m n : (Σ k, ι k) →₀ ℕ) : bdeg (m + n) = bdeg m + bdeg n := by
  funext k
  simp [bdeg, Finset.sum_add_distrib]

theorem isMultiHomog_iff {s : MRingOver ℂ ι} {a : K → ℕ} :
    IsMultiHomog s a ↔ ∀ m, coeff m s ≠ 0 → bdeg m = a := by
  constructor
  · intro h m hm
    funext k
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    exact congrFun (h m (mem_support_iff.mp hm)) k

theorem bdeg_of_mem {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ s.support) : bdeg m = a := by
  funext k
  exact hs m hm k

theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℂ) :
    IsMultiHomog (monomial m c : MRingOver ℂ ι) (bdeg m) := by
  classical
  rw [isMultiHomog_iff]
  intro n hn
  rw [coeff_monomial] at hn
  split_ifs at hn with h
  · rw [h]
  · exact absurd rfl hn

theorem isMultiHomog_mul {f g : MRingOver ℂ ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  rw [isMultiHomog_iff] at hf hg ⊢
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver ℂ ι) 0 := by
  classical
  rw [isMultiHomog_iff]
  intro m hm
  rw [coeff_one] at hm
  split_ifs at hm with h
  · subst h
    funext k
    simp [bdeg]
  · exact absurd rfl hm

theorem isMultiHomog_pow {f : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using isMultiHomog_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

theorem isMultiHomog_add {f g : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  rw [isMultiHomog_iff] at hf hg ⊢
  intro m hm
  rw [coeff_add] at hm
  by_cases h0 : coeff m f = 0
  · rw [h0, zero_add] at hm
    exact hg m hm
  · exact hf m h0

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver ℂ ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_C_mul {f : MRingOver ℂ ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : ℂ) :
    IsMultiHomog (C c * f) a := by
  rw [isMultiHomog_iff] at hf ⊢
  intro m hm
  rw [coeff_C_mul] at hm
  exact hf m (right_ne_zero_of_mul hm)

theorem isMultiHomog_sum {α : Type} (s : Finset α) (f : α → MRingOver ℂ ι) {a : K → ℕ}
    (h : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_zero a
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact isMultiHomog_add (h j (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem isMultiHomog_prod {α : Type} (s : Finset α) (f : α → MRingOver ℂ ι) (a : α → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (a j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self _ _))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

open Classical in

def wt (p : Σ k, ι k) : K → ℕ := fun k => if p.1 = k then 1 else 0

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) : Finsupp.weight wt m = bdeg m := by
  classical
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • wt i) (fun _ => zero_smul _ _)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wt, bdeg]
  rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
  simp

def cmp (D : K → ℕ) : MRingOver ℂ ι →ₗ[ℂ] MRingOver ℂ ι := weightedHomogeneousComponent wt D

theorem coeff_cmp (D : K → ℕ) (p : MRingOver ℂ ι) (m : (Σ k, ι k) →₀ ℕ) :
    coeff m (cmp D p) = if bdeg m = D then coeff m p else 0 := by
  classical
  rw [cmp, coeff_weightedHomogeneousComponent, weight_wt]

theorem isMultiHomog_cmp (D : K → ℕ) (p : MRingOver ℂ ι) : IsMultiHomog (cmp D p) D := by
  rw [isMultiHomog_iff]
  intro m hm
  rw [coeff_cmp] at hm
  by_contra h
  exact hm (if_neg h)

theorem cmp_of_homog {h : MRingOver ℂ ι} {b : K → ℕ} (hh : IsMultiHomog h b) (D : K → ℕ) :
    cmp D h = if b = D then h else 0 := by
  rw [isMultiHomog_iff] at hh
  ext m
  rw [coeff_cmp]
  by_cases hm : coeff m h = 0
  · split_ifs <;> simp [hm]
  · by_cases hb : b = D
    · subst hb
      simp [hh m hm]
    · rw [if_neg hb, coeff_zero, if_neg (by rw [hh m hm]; exact hb)]

open Classical in

theorem cmp_mul {q : MRingOver ℂ ι} {d : K → ℕ} (hq : IsMultiHomog q d) (D : K → ℕ)
    (p : MRingOver ℂ ι) : cmp D (p * q) = if d ≤ D then cmp (D - d) p * q else 0 := by
  classical
  rw [isMultiHomog_iff] at hq
  ext m
  rw [coeff_cmp]
  by_cases hdD : d ≤ D <;> by_cases hm : bdeg m = D <;> simp only [hdD, hm, if_true, if_false]
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_cmp]
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      rw [if_pos]
      funext k
      have h3 := congrFun hm k
      have h4 := hdD k
      rw [← hx, bdeg_add, h2] at h3
      simp only [Pi.add_apply] at h3
      simp only [Pi.sub_apply]
      omega
  · rw [coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_cmp]
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      rw [if_neg, zero_mul]
      intro h1
      apply hm
      funext k
      have h3 := congrFun h1 k
      have h4 := hdD k
      rw [← hx, bdeg_add, h2]
      simp only [Pi.add_apply, Pi.sub_apply] at h3 ⊢
      rw [h3]
      exact Nat.sub_add_cancel h4
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    by_cases hq0 : coeff x.2 q = 0
    · simp [hq0]
    · exfalso
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have h2 := hq x.2 hq0
      apply hdD
      intro k
      have h3 := congrFun hm k
      rw [← hx, bdeg_add, h2] at h3
      simp only [Pi.add_apply] at h3
      rw [← h3]
      exact Nat.le_add_left _ _
  · rw [coeff_zero]

theorem eval_cmp_eq_zero {S : Set (MRingOver ℂ ι)} (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ s ∈ S, eval z s = 0) {x : MRingOver ℂ ι} (hx : x ∈ Ideal.span S) :
    ∀ D : K → ℕ, eval z (cmp D x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro D
    obtain ⟨b, hb⟩ := hS x hx
    rw [cmp_of_homog hb]
    split_ifs
    · exact hz x hx
    · simp
  | zero => intro D; simp
  | add x y _ _ hx hy => intro D; rw [map_add, map_add, hx, hy, add_zero]
  | smul a x _ hx =>
    intro D
    rw [smul_eq_mul, as_sum a, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [mul_comm, cmp_mul (isMultiHomog_monomial ν _)]
    split_ifs
    · rw [map_mul, hx, zero_mul]
    · simp

open Classical in

def spike (j : ∀ k, ι k) (f : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p => if p.2 = j p.1 then f p.1 else 0)

open Classical in
theorem spike_apply (j : ∀ k, ι k) (f : K → ℕ) (p : Σ k, ι k) :
    spike j f p = if p.2 = j p.1 then f p.1 else 0 := by
  classical
  simp only [spike, Finsupp.coe_equivFunOnFinite_symm]

theorem bdeg_spike (j : ∀ k, ι k) (f : K → ℕ) : bdeg (spike j f) = f := by
  classical
  funext k
  simp [bdeg, spike_apply]

theorem eval_spike (j : ∀ k, ι k) (f : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (monomial (spike j f) 1) = ∏ k, z ⟨k, j k⟩ ^ f k := by
  classical
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (j k) (fun i _ hi => by simp [spike_apply, hi]) (by simp)]
  simp [spike_apply]

theorem exists_pow_mem {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι}
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ r : ℕ, ∀ c : (∀ k, ι k), monomial (spike c (fun _ => r)) (1 : ℂ) ∈ Ideal.span (insert G S) := by
  classical
  have key : ∀ c : (∀ k, ι k), ∃ n : ℕ,
      (monomial (spike c (fun _ => 1)) (1 : ℂ)) ^ n ∈ Ideal.span (insert G S) := by
    intro c
    have hmem : monomial (spike c (fun _ => 1)) (1 : ℂ) ∈
        vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span (insert G S))) := by
      rw [mem_vanishingIdeal_iff]
      intro x hx
      rw [mem_zeroLocus_iff] at hx
      have hxJ : ∀ p ∈ Ideal.span (insert G S), eval x p = 0 := fun p hp => by
        simpa [coe_aeval_eq_eval] using hx p hp
      have hG := hxJ G (Ideal.subset_span (Set.mem_insert _ _))
      have hS : ∀ s ∈ S, eval x s = 0 := fun s hs =>
        hxJ s (Ideal.subset_span (Set.mem_insert_of_mem _ hs))
      have hnc : ¬ ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := fun hc => hcone x hc hS hG
      push_neg at hnc
      obtain ⟨k, hk⟩ := hnc
      have h0 : eval x (monomial (spike c (fun _ => 1)) (1 : ℂ)) = 0 := by
        rw [eval_spike]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      simpa [coe_aeval_eq_eval] using h0
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  choose n hn using key
  refine ⟨∑ c, n c, fun c => ?_⟩
  have hle : n c ≤ ∑ c, n c := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have heq : monomial (spike c (fun _ => ∑ c, n c)) (1 : ℂ) =
      (monomial (spike c (fun _ => 1)) 1) ^ n c * (monomial (spike c (fun _ => 1)) 1) ^ (∑ c, n c - n c) := by
    have hexp : (∑ c, n c) • spike c (fun _ => 1) = spike c (fun _ => ∑ c, n c) := by
      ext p
      rw [Finsupp.smul_apply, spike_apply, spike_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [← pow_add, Nat.add_sub_cancel' hle, monomial_pow, one_pow, hexp]
  rw [heq]
  exact Ideal.mul_mem_right _ _ (hn c)

theorem rel_one {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ}
    (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a) (hG : IsMultiHomog G e) (he : ∀ k, 1 ≤ e k)
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ N₀ : ℕ, ∀ M : ℕ, N₀ ≤ M → ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = (M + 1) • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (M • e) ∧
        ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z (monomial μ (1 : ℂ)) = eval z h * eval z G := by
  classical
  obtain ⟨r, hr⟩ := exists_pow_mem hcone
  refine ⟨r * ∑ k, Fintype.card (ι k), fun M hM μ hμ => ?_⟩
  have hc : ∀ k, ∃ i, r ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    push_neg at hne
    have h1 : bdeg μ k ≤ Fintype.card (ι k) * r := by
      calc bdeg μ k = ∑ i, μ ⟨k, i⟩ := rfl
        _ ≤ ∑ _i : ι k, r := Finset.sum_le_sum fun i _ => (hne i).le
        _ = Fintype.card (ι k) * r := by simp
    have h2 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : bdeg μ k = (M + 1) * e k := by rw [hμ]; simp
    have h4 := he k
    have h5 : Fintype.card (ι k) * r ≤ (∑ k, Fintype.card (ι k)) * r := Nat.mul_le_mul_right r h2
    have h6 : (M + 1) * 1 ≤ (M + 1) * e k := Nat.mul_le_mul_left (M + 1) h4
    nlinarith
  choose c hc using hc
  have hle : spike c (fun _ => r) ≤ μ := by
    rw [Finsupp.le_def]
    rintro ⟨k, i⟩
    rw [spike_apply]
    split_ifs with h
    · simp only at h
      subst h
      exact hc k
    · exact Nat.zero_le _
  have hmem : monomial μ (1 : ℂ) ∈ Ideal.span (insert G S) := by
    have : monomial μ (1 : ℂ) = monomial (spike c (fun _ => r)) 1 * monomial (μ - spike c (fun _ => r)) 1 := by
      rw [monomial_mul, mul_one, add_tsub_cancel_of_le hle]
    rw [this]
    exact Ideal.mul_mem_right _ _ (hr c)
  obtain ⟨a, s, hs, hμa⟩ := Ideal.mem_span_insert.1 hmem
  have heD : e ≤ (M + 1) • e := fun k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  have hDe : (M + 1) • e - e = M • e := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  refine ⟨cmp (M • e) a, isMultiHomog_cmp _ _, fun z hz => ?_⟩
  have h1 : monomial μ (1 : ℂ) = cmp ((M + 1) • e) (a * G) + cmp ((M + 1) • e) s := by
    rw [← map_add, ← hμa, cmp_of_homog (isMultiHomog_monomial μ 1), if_pos hμ]
  rw [h1, map_add, cmp_mul hG, if_pos heD, hDe, map_mul, eval_cmp_eq_zero hS hz hs, add_zero]

theorem rel_direct {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e)
    {N₀ M : ℕ} (hM : M ≤ N₀) (μ : (Σ k, ι k) →₀ ℕ) (hμ : bdeg μ = M • e) :
    ∃ h : MRingOver ℂ ι, IsMultiHomog h (N₀ • e) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) →
      eval z (monomial μ (1 : ℂ)) * eval z G ^ N₀ = eval z h * eval z G ^ M := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hM
  refine ⟨monomial μ 1 * G ^ t, ?_, fun z _ => ?_⟩
  · have := isMultiHomog_mul (isMultiHomog_monomial μ 1) (isMultiHomog_pow hG t)
    rw [hμ, ← add_smul] at this
    exact this
  · rw [map_mul, map_pow, pow_add]
    ring

theorem eval_eq_sum_support (p : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) :
    eval z p = ∑ ν ∈ p.support, coeff ν p * eval z (monomial ν 1) := by
  conv_lhs => rw [as_sum p]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [eval_monomial, eval_monomial]
  ring

theorem rel_all {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e) (N₀ : ℕ)
    (hN₀ : ∀ M : ℕ, N₀ ≤ M → ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = (M + 1) • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (M • e) ∧
        ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z (monomial μ (1 : ℂ)) = eval z h * eval z G)
    (M : ℕ) : ∀ μ : (Σ k, ι k) →₀ ℕ, bdeg μ = M • e →
      ∃ h : MRingOver ℂ ι, IsMultiHomog h (N₀ • e) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) →
        eval z (monomial μ (1 : ℂ)) * eval z G ^ N₀ = eval z h * eval z G ^ M := by
  induction M with
  | zero => exact fun μ hμ => rel_direct hG (Nat.zero_le _) μ hμ
  | succ M ih =>
    intro μ hμ
    by_cases hM : M + 1 ≤ N₀
    · exact rel_direct hG hM μ hμ
    · obtain ⟨h₁, hh₁, hev⟩ := hN₀ M (by omega) μ hμ
      choose! H hH hHev using ih
      refine ⟨∑ ν ∈ h₁.support, C (coeff ν h₁) * H ν,
        isMultiHomog_sum _ _ fun ν hν => isMultiHomog_C_mul (hH ν (bdeg_of_mem hh₁ hν)) _, fun z hz => ?_⟩
      rw [hev z hz, eval_eq_sum_support h₁ z, map_sum]
      simp only [map_mul, eval_C]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν hν => ?_
      have := hHev ν (bdeg_of_mem hh₁ hν) z hz
      calc coeff ν h₁ * eval z (monomial ν 1) * eval z G * eval z G ^ N₀
          = coeff ν h₁ * (eval z (monomial ν 1) * eval z G ^ N₀) * eval z G := by ring
        _ = _ := by rw [this]; ring

def Mon (D : K → ℕ) : Set ((Σ k, ι k) →₀ ℕ) := {ν | bdeg ν = D}

theorem mon_finite (D : K → ℕ) : (Mon (ι := ι) D).Finite := by
  classical
  apply (Set.finite_Icc (0 : (Σ k, ι k) →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun p => D p.1)).subset
  intro ν hν
  have hν' : bdeg ν = D := hν
  refine ⟨zero_le, ?_⟩
  rw [Finsupp.le_def]
  rintro ⟨k, i⟩
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [← hν']
  exact Finset.single_le_sum (f := fun i => ν ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

instance (D : K → ℕ) : Finite (Mon (ι := ι) D) := (mon_finite D).to_subtype

noncomputable instance (D : K → ℕ) : Fintype (Mon (ι := ι) D) := Fintype.ofFinite _

theorem eval_eq_sum_mon {h : MRingOver ℂ ι} {D : K → ℕ} (hh : IsMultiHomog h D) (z : (Σ k, ι k) → ℂ) :
    eval z h = ∑ ν : Mon (ι := ι) D, coeff ν.1 h * eval z (monomial ν.1 1) := by
  classical
  rw [eval_eq_sum_support, ← Finset.sum_subtype (mon_finite D).toFinset (fun x => Set.Finite.mem_toFinset _)
    (fun ν => coeff ν h * eval z (monomial ν 1))]
  apply Finset.sum_subset
  · intro ν hν
    rw [Set.Finite.mem_toFinset]
    exact bdeg_of_mem hh hν
  · intro ν _ hν
    rw [mem_support_iff, not_not] at hν
    rw [hν, zero_mul]

def phi (G : MRingOver ℂ ι) (e : K → ℕ) (N₀ : ℕ) (z : (Σ k, ι k) → ℂ) : Mon (ι := ι) (N₀ • e) → ℂ :=
  fun ν => eval z (monomial ν.1 1) / eval z G ^ N₀

theorem exists_rep {S : Set (MRingOver ℂ ι)} {G : MRingOver ℂ ι} {e : K → ℕ}
    (hS : ∀ s ∈ S, ∃ a, IsMultiHomog s a) (hG : IsMultiHomog G e) (he : ∀ k, 1 ≤ e k)
    (hcone : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0) :
    ∃ N₀ : ℕ, ∀ (M : ℕ) (F : MRingOver ℂ ι), IsMultiHomog F (M • e) →
      ∃ d : Mon (ι := ι) (N₀ • e) → ℂ, ∀ z : (Σ k, ι k) → ℂ, (∀ s ∈ S, eval z s = 0) → eval z G ≠ 0 →
        eval z F / eval z G ^ M = ∑ ν, d ν * phi G e N₀ z ν := by
  obtain ⟨N₀, hN₀⟩ := rel_one hS hG he hcone
  refine ⟨N₀, fun M F hF => ?_⟩
  have hrel := rel_all hG N₀ hN₀ M
  choose! H hH hHev using hrel
  refine ⟨fun ν => ∑ μ ∈ F.support, coeff μ F * coeff ν.1 (H μ), fun z hz hGz => ?_⟩
  have hGM : eval z G ^ M ≠ 0 := pow_ne_zero _ hGz
  have hGN : eval z G ^ N₀ ≠ 0 := pow_ne_zero _ hGz
  rw [eval_eq_sum_support F, Finset.sum_div]
  simp only [phi, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hμd := bdeg_of_mem hF hμ
  have e1 : eval z (monomial μ 1) / eval z G ^ M = eval z (H μ) / eval z G ^ N₀ := by
    rw [div_eq_div_iff hGM hGN]
    exact hHev μ hμd z hz
  rw [mul_div_assoc, e1, eval_eq_sum_mon (hH μ hμd), Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

theorem phi_smul {G : MRingOver ℂ ι} {e : K → ℕ} (hG : IsMultiHomog G e) (N₀ : ℕ) (r : K → ℂ)
    (hr : ∀ k, r k ≠ 0) (w : (Σ k, ι k) → ℂ) :
    phi G e N₀ (fun p => r p.1 * w p) = phi G e N₀ w := by
  funext ν
  simp only [phi]
  rw [FibreRepresentatives.eval_smul (isMultiHomog_monomial ν.1 1) r w, FibreRepresentatives.eval_smul hG r w]
  have hν : bdeg ν.1 = N₀ • e := ν.2
  rw [hν]
  have hP : (∏ k, r k ^ e k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hr k)
  have hpow : (∏ k, r k ^ (N₀ • e) k) = (∏ k, r k ^ e k) ^ N₀ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]
  rw [hpow, mul_pow, mul_div_mul_left _ _ (pow_ne_zero _ hP)]

open Classical in

theorem isMultiHomog_X (k : K) (a : ι k) :
    IsMultiHomog (X ⟨k, a⟩ : MRingOver ℂ ι) (fun k' => if k' = k then 1 else 0) := by
  classical
  have := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, a⟩ : Σ k, ι k) 1) (1 : ℂ)
  rw [show (X ⟨k, a⟩ : MRingOver ℂ ι) = monomial (Finsupp.single ⟨k, a⟩ 1) 1 from rfl]
  convert this using 1
  funext k'
  by_cases h : k' = k
  · subst h
    simp [bdeg, Finsupp.single_apply]
  · simp only [if_neg h, bdeg]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

theorem exists_sep {e : K → ℕ} (he : ∀ k, 1 ≤ e k) {z w : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (hn : ¬ ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * w p) :
    ∃ Q : MRingOver ℂ ι, IsMultiHomog Q e ∧ eval w Q = 0 ∧ eval z Q ≠ 0 := by
  classical
  have hmin : ∃ k a b, z ⟨k, a⟩ * w ⟨k, b⟩ ≠ z ⟨k, b⟩ * w ⟨k, a⟩ := by
    by_contra hc
    push_neg at hc
    apply hn
    choose i hi using hw
    refine ⟨fun k => z ⟨k, i k⟩ / w ⟨k, i k⟩, fun k h0 => ?_, ?_⟩
    · rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · obtain ⟨a, ha⟩ := hz k
        have := hc k a (i k)
        rw [h0, zero_mul] at this
        exact ha ((mul_eq_zero.1 this).resolve_right (hi k))
      · exact hi k h0
    · funext ⟨k, a⟩
      simp only
      rw [div_mul_eq_mul_div, eq_div_iff (hi k)]
      exact hc k a (i k)
  obtain ⟨k, a, b, hab⟩ := hmin
  choose j hj using hz
  let δ : K → ℕ := fun k' => if k' = k then 1 else 0
  let L : MRingOver ℂ ι := C (w ⟨k, b⟩) * X ⟨k, a⟩ + C (-w ⟨k, a⟩) * X ⟨k, b⟩
  have hL : IsMultiHomog L δ :=
    isMultiHomog_add (isMultiHomog_C_mul (isMultiHomog_X k a) _) (isMultiHomog_C_mul (isMultiHomog_X k b) _)
  refine ⟨L * monomial (spike j (e - δ)) 1, ?_, ?_, ?_⟩
  · have := isMultiHomog_mul hL (isMultiHomog_monomial (spike j (e - δ)) (1 : ℂ))
    rw [bdeg_spike] at this
    convert this using 1
    funext k'
    have := he k'
    simp only [Pi.add_apply, Pi.sub_apply, δ]
    split_ifs <;> omega
  · rw [map_mul]
    apply mul_eq_zero_of_left
    simp only [L, map_add, map_mul, eval_C, eval_X]
    ring
  · rw [map_mul]
    refine mul_ne_zero ?_ ?_
    · simp only [L, map_add, map_mul, eval_C, eval_X]
      intro h
      apply hab
      linear_combination h
    · rw [eval_spike]
      exact Finset.prod_ne_zero_iff.2 fun k' _ => pow_ne_zero _ (hj k')

end AvoidFormFinite

open AvoidFormFinite in

theorem AvoidFormFinite.proof : AvoidFormFinite.Statement := by
  intro K _ ι _ S G e he hG hS hcone
  classical
  obtain ⟨N₀, hrep⟩ := exists_rep hS hG he hcone
  let P : ((Σ k, ι k) → ℂ) → Prop := fun z => (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ s ∈ S, eval z s = 0
  let V : Set (Mon (ι := ι) (N₀ • e) → ℂ) := Set.range (fun z : {z // P z} => phi G e N₀ z.1)
  have horb : ∀ z t, P z → P t → phi G e N₀ z = phi G e N₀ t →
      ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * t p := by
    intro z t hz ht hzt
    by_contra hn
    obtain ⟨Q, hQ, hQt, hQz⟩ := exists_sep he hz.1 ht.1 hn
    obtain ⟨d, hd⟩ := hrep 1 Q (by rw [one_smul]; exact hQ)
    have h1 := hd z hz.2 (hcone z hz.1 hz.2)
    have h2 := hd t ht.2 (hcone t ht.1 ht.2)
    rw [hzt, ← h2, hQt, zero_div, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact hQz h1
    · exact pow_ne_zero _ (hcone z hz.1 hz.2) h1
  choose pre hpre0 using fun v : V => v.2
  have hpre : ∀ v : V, phi G e N₀ (pre v).1 = v := fun v => hpre0 v
  have hli : LinearIndependent ℂ (fun v : V => (v : Mon (ι := ι) (N₀ • e) → ℂ)) := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    have hsep : ∀ j ∈ s.erase i, ∃ Q : MRingOver ℂ ι, IsMultiHomog Q e ∧ eval (pre j).1 Q = 0 ∧
        eval (pre i).1 Q ≠ 0 := by
      intro j hj
      refine exists_sep he (pre i).2.1 (pre j).2.1 ?_
      rintro ⟨r, hr, hrz⟩
      apply (Finset.mem_erase.1 hj).1
      apply Subtype.ext
      rw [← hpre j, ← hpre i, hrz, phi_smul hG N₀ r hr]
    choose! Q hQe hQz hQi using hsep
    have hF := isMultiHomog_prod (s.erase i) Q (fun _ => e) hQe
    rw [Finset.sum_const] at hF
    obtain ⟨d, hd⟩ := hrep _ _ hF
    have hval : ∀ v : V, ∑ ν, d ν * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν =
        eval (pre v).1 (∏ j ∈ s.erase i, Q j) / eval (pre v).1 G ^ (s.erase i).card := by
      intro v
      rw [hd _ (pre v).2.2 (hcone _ (pre v).2.1 (pre v).2.2), hpre v]
    have h0 : ∑ v ∈ s, g v * (eval (pre v).1 (∏ j ∈ s.erase i, Q j) /
        eval (pre v).1 G ^ (s.erase i).card) = 0 := by
      simp_rw [← hval]
      have hz : ∀ ν, ∑ v ∈ s, g v * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν = 0 := fun ν => by
        have := congrFun hsum ν
        simpa [Finset.sum_apply] using this
      calc ∑ v ∈ s, g v * ∑ ν, d ν * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν
          = ∑ ν, d ν * ∑ v ∈ s, g v * (v : Mon (ι := ι) (N₀ • e) → ℂ) ν := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by simp [hz]
    rw [Finset.sum_eq_single i (fun v hv hvi => by
      rw [map_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hvi, hv⟩) (hQz v (Finset.mem_erase.2 ⟨hvi, hv⟩)),
        zero_div, mul_zero]) (fun h => absurd hi h)] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exfalso
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · rw [map_prod] at h
        exact (Finset.prod_ne_zero_iff.2 fun j hj => hQi j hj) h
      · exact pow_ne_zero _ (hcone _ (pre i).2.1 (pre i).2.2) h
  haveI : Finite V := hli.finite_of_isNoetherian
  haveI := Fintype.ofFinite V
  refine ⟨Finset.univ.image fun v => (pre v).1, fun z hz hzS => ?_⟩
  let v : V := ⟨phi G e N₀ z, ⟨z, hz, hzS⟩, rfl⟩
  exact ⟨(pre v).1, Finset.mem_image_of_mem _ (Finset.mem_univ v),
    horb z (pre v).1 ⟨hz, hzS⟩ (pre v).2 (hpre v).symm⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
