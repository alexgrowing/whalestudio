import Formalism.MahlerMeasure.HasOrder
import Formalism.MahlerMeasure.FinalM

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset

section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

noncomputable def wf (m : σ →₀ ℕ) : K := ∏ x, ((m x).factorial : K)

theorem prod_eq_wf (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : K)) = wf m := by
  unfold wf; exact Finsupp.prod_fintype _ _ (by simp)

theorem wf_add_single (m : σ →₀ ℕ) (i : σ) :
    (wf (m + Finsupp.single i 1) : K) = ((m i + 1 : ℕ) : K) * wf m := by
  unfold wf
  have h : ∀ x : σ, (((m + Finsupp.single i 1 : σ →₀ ℕ) x).factorial : K) =
      ((m x).factorial : K) * (if x = i then ((m i + 1 : ℕ) : K) else 1) := by
    intro x
    by_cases hx : x = i
    · subst hx; simp [Nat.factorial_succ]; ring
    · simp [hx, Finsupp.single_apply]
  rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp [mul_comm]

noncomputable def fk (F G : MvPolynomial σ K) : K :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * wf m

theorem fk_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (h : F.support ⊆ s) :
    fk F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by
  unfold fk
  apply Finset.sum_subset h
  intro m _ hm
  rw [notMem_support_iff.mp hm]; ring

theorem fk_eq_sum' (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (h : G.support ⊆ s) :
    fk F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by
  rw [fk_eq_sum F G (F.support ∪ s) Finset.subset_union_left]
  symm
  apply Finset.sum_subset Finset.subset_union_right
  intro m _ hm
  rw [notMem_support_iff.mp (fun h' => hm (h h'))]; ring

theorem fk_symm (F G : MvPolynomial σ K) : fk F G = fk G F := by
  rw [fk_eq_sum F G _ (Finset.subset_union_left (s₂ := G.support)),
    fk_eq_sum G F _ (Finset.subset_union_right (s₁ := F.support))]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem fk_add_left (F F' G : MvPolynomial σ K) : fk (F + F') G = fk F G + fk F' G := by
  rw [fk_eq_sum (F + F') G (F.support ∪ F'.support) support_add,
    fk_eq_sum F G _ (Finset.subset_union_left (s₂ := F'.support)),
    fk_eq_sum F' G _ (Finset.subset_union_right (s₁ := F.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_add]; ring)

theorem fk_smul_left (c : K) (F G : MvPolynomial σ K) : fk (c • F) G = c * fk F G := by
  rw [fk_eq_sum (c • F) G F.support support_smul, fk, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_smul, smul_eq_mul]; ring)

theorem fk_zero_left (G : MvPolynomial σ K) : fk 0 G = 0 := by simp [fk]

theorem fk_neg_left (F G : MvPolynomial σ K) : fk (-F) G = - fk F G := by
  rw [show -F = (-1 : K) • F by simp, fk_smul_left]; ring

theorem fk_sub_left (F F' G : MvPolynomial σ K) : fk (F - F') G = fk F G - fk F' G := by
  rw [sub_eq_add_neg, fk_add_left, fk_neg_left]; ring

theorem fk_sum_left {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fk (∑ i ∈ t, F i) G = ∑ i ∈ t, fk (F i) G := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fk_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fk_add_left, ih]

theorem fk_add_right (F G G' : MvPolynomial σ K) : fk F (G + G') = fk F G + fk F G' := by
  rw [fk_symm, fk_add_left, fk_symm G, fk_symm G']

theorem fk_smul_right (c : K) (F G : MvPolynomial σ K) : fk F (c • G) = c * fk F G := by
  rw [fk_symm, fk_smul_left, fk_symm]

theorem fk_sub_right (F G G' : MvPolynomial σ K) : fk F (G - G') = fk F G - fk F G' := by
  rw [fk_symm, fk_sub_left, fk_symm G, fk_symm G']

theorem fk_zero_right (F : MvPolynomial σ K) : fk F 0 = 0 := by rw [fk_symm, fk_zero_left]

theorem fk_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ K) (G : ι → MvPolynomial σ K) :
    fk F (∑ i ∈ t, G i) = ∑ i ∈ t, fk F (G i) := by
  rw [fk_symm, fk_sum_left]; exact Finset.sum_congr rfl (fun i _ => fk_symm _ _)

theorem fk_X_mul (i : σ) (g h : MvPolynomial σ K) : fk (X i * g) h = fk g (pderiv i h) := by
  have hs : (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by
    rw [mul_comm]; exact support_mul_X i g
  rw [fk, hs, Finset.sum_map, fk]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [addRightEmbedding_apply]
  rw [mul_comm (X i) g, coeff_mul_X, coeff_pderiv, wf_add_single]
  push_cast; ring

end

section tie
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem fk_E (g h : MvPolynomial σ K) : fk (Formalism.GM.tieE w e g) h = fk g (Formalism.GM.tieF w e h) := by
  have h1 : Formalism.GM.tieE w e g = ∑ c, X (e c) * (X (w c) * g) := by
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have h2 : Formalism.GM.tieF w e h = ∑ c, pderiv (w c) (pderiv (e c) h) := by
    simp [Formalism.GM.tieF, LinearMap.sum_apply]
  rw [h1, h2, fk_sum_left, fk_sum_right]
  exact Finset.sum_congr rfl (fun c _ => by rw [fk_X_mul, fk_X_mul])

theorem fk_E_pow (j : ℕ) (g h : MvPolynomial σ K) :
    fk ((Formalism.GM.tieE w e ^ j) g) h = fk g ((Formalism.GM.tieF w e ^ j) h) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, fk_E, ih, pow_succ, Module.End.mul_apply]

end tie

section real
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem wf_pos (m : σ →₀ ℕ) : (0 : ℝ) < wf m :=
  Finset.prod_pos (fun x _ => by exact_mod_cast Nat.factorial_pos _)

theorem fk_self_nonneg (F : MvPolynomial σ ℝ) : 0 ≤ fk F F :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (mul_self_nonneg _) (wf_pos m).le)

theorem fk_abs_le (F G : MvPolynomial σ ℝ) : 2 * |fk F G| ≤ fk F F + fk G G := by
  have h1 := fk_self_nonneg (F - G)
  have h2 := fk_self_nonneg (F + G)
  rw [fk_sub_left, fk_sub_right, fk_sub_right, fk_symm G F] at h1
  rw [fk_add_left, fk_add_right, fk_add_right, fk_symm G F] at h2
  have : 2 * |fk F G| = |2 * fk F G| := by rw [abs_mul, abs_two]
  rw [this, abs_le]
  constructor <;> linarith

end real

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem biHom_zero (a b : ℕ) : BiHom w e a b (0 : MvPolynomial σ K) := by
  intro m hm; simp at hm

theorem biHom_add {a b : ℕ} {u v : MvPolynomial σ K} (hu : BiHom w e a b u) (hv : BiHom w e a b v) :
    BiHom w e a b (u + v) := by
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hu m h
  · exact hv m h

theorem biHom_smul {a b : ℕ} (c : K) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e a b (c • u) := fun m hm => hu m (support_smul hm)

theorem biHom_neg {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) : BiHom w e a b (-u) := by
  rw [show -u = (-1 : K) • u by simp]; exact biHom_smul _ hu

theorem biHom_sub {a b : ℕ} {u v : MvPolynomial σ K} (hu : BiHom w e a b u) (hv : BiHom w e a b v) :
    BiHom w e a b (u - v) := by
  rw [sub_eq_add_neg]; exact biHom_add hu (biHom_neg hv)

theorem biHom_sum {ι : Type} {a b : ℕ} (t : Finset ι) (u : ι → MvPolynomial σ K)
    (hu : ∀ i ∈ t, BiHom w e a b (u i)) : BiHom w e a b (∑ i ∈ t, u i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using biHom_zero a b
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact biHom_add (hu x (Finset.mem_insert_self _ _)) (ih (fun i hi => hu i (Finset.mem_insert_of_mem hi)))

theorem support_X_mul (i : σ) (g : MvPolynomial σ K) :
    (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by
  rw [mul_comm]; exact support_mul_X i g

variable (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem sum_single_w (c : Fin r) : (∑ c', (Finsupp.single (w c) 1 : σ →₀ ℕ) (w c')) = 1 := by
  simp [Finsupp.single_apply, hw.eq_iff]

theorem sum_single_e (c : Fin r) : (∑ c', (Finsupp.single (e c) 1 : σ →₀ ℕ) (e c')) = 1 := by
  simp [Finsupp.single_apply, he.eq_iff]

theorem sum_single_we (c : Fin r) : (∑ c', (Finsupp.single (w c) 1 : σ →₀ ℕ) (e c')) = 0 := by
  simp [Finsupp.single_apply, hwe]

theorem sum_single_ew (c : Fin r) : (∑ c', (Finsupp.single (e c) 1 : σ →₀ ℕ) (w c')) = 0 := by
  simp [Finsupp.single_apply, fun c' => Ne.symm (hwe c' c)]

theorem biHom_X_w {a b : ℕ} (c : Fin r) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a + 1) b (X (w c) * u) := by
  intro m hm
  rw [support_X_mul, Finset.mem_map] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib]
  rw [sum_single_w hw he hwe, sum_single_we hw he hwe, (hu m0 hm0).1, (hu m0 hm0).2]
  simp

theorem biHom_X_e {a b : ℕ} (c : Fin r) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e a (b + 1) (X (e c) * u) := by
  intro m hm
  rw [support_X_mul, Finset.mem_map] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib]
  rw [sum_single_e hw he hwe, sum_single_ew hw he hwe, (hu m0 hm0).1, (hu m0 hm0).2]
  simp

theorem biHom_E {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a + 1) (b + 1) (tieE w e u) := by
  rw [tieE_apply', Finset.sum_mul]
  apply biHom_sum
  intro c _
  rw [mul_assoc]
  exact biHom_X_w hw he hwe c (biHom_X_e hw he hwe c hu)

theorem biHom_E_pow {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) (l : ℕ) :
    BiHom w e (a + l) (b + l) ((tieE w e ^ l) u) := by
  induction l with
  | zero => simpa using hu
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact biHom_E hw he hwe ih

theorem biHom_pderiv_w {a b : ℕ} (c : Fin r) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a - 1) b (pderiv (w c) u) ∧ (a = 0 → pderiv (w c) u = 0) := by
  have key : ∀ m ∈ (pderiv (w c) u).support, (∑ c', m (w c')) + 1 = a ∧ (∑ c', m (e c')) = b := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h2 : m + Finsupp.single (w c) 1 ∈ u.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have h3 := hu _ h2
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h3
    rw [sum_single_w hw he hwe, sum_single_we hw he hwe] at h3
    simpa using h3
  refine ⟨fun m hm => ?_, fun ha => ?_⟩
  · have := key m hm; exact ⟨by omega, this.2⟩
  · ext m
    by_contra h
    have := key m (mem_support_iff.mpr (by simpa using h))
    omega

theorem biHom_pderiv_e {a b : ℕ} (c : Fin r) {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e a (b - 1) (pderiv (e c) u) ∧ (b = 0 → pderiv (e c) u = 0) := by
  have key : ∀ m ∈ (pderiv (e c) u).support, (∑ c', m (w c')) = a ∧ (∑ c', m (e c')) + 1 = b := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h2 : m + Finsupp.single (e c) 1 ∈ u.support := mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have h3 := hu _ h2
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h3
    rw [sum_single_e hw he hwe, sum_single_ew hw he hwe] at h3
    simpa using h3
  refine ⟨fun m hm => ?_, fun hb => ?_⟩
  · have := key m hm; exact ⟨this.1, by omega⟩
  · ext m
    by_contra h
    have := key m (mem_support_iff.mpr (by simpa using h))
    omega

theorem biHom_F {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a - 1) (b - 1) (tieF w e u) ∧ (a = 0 ∨ b = 0 → tieF w e u = 0) := by
  rw [tieF_apply']
  refine ⟨biHom_sum _ _ (fun c _ => ?_), fun h => Finset.sum_eq_zero (fun c _ => ?_)⟩
  · exact (biHom_pderiv_w hw he hwe c (biHom_pderiv_e hw he hwe c hu).1).1
  · rcases h with h | h
    · exact (biHom_pderiv_w hw he hwe c (biHom_pderiv_e hw he hwe c hu).1).2 h
    · rw [(biHom_pderiv_e hw he hwe c hu).2 h, map_zero]

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem FE_one {a b : ℕ} {g : MvPolynomial σ K} (hg : BiHom w e a b g) :
    tieF w e (tieE w e g) = tieE w e (tieF w e g) + ((a + b + r : ℕ) : K) • g := by
  rw [tieE_apply', tieF_apply', F_S_mul hw he hwe g a b (euler_w_of_biHom w e hg) (euler_e_of_biHom w e hg),
    ← tieF_apply', ← tieE_apply']

theorem F_E_pow_gen {a b : ℕ} {y : MvPolynomial σ K} (hy : BiHom w e a b y) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) y) =
      (tieE w e ^ (j + 1)) (tieF w e y) + (((j + 1) * (a + b + r + j) : ℕ) : K) • (tieE w e ^ j) y := by
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, one_mul, add_zero]
    exact FE_one hw he hwe hy
  | succ j ih =>
    have h2 := biHom_E_pow hw he hwe hy (j + 1)
    rw [show tieE w e ^ (j + 1 + 1) = tieE w e * tieE w e ^ (j + 1) from pow_succ' _ _,
      Module.End.mul_apply, FE_one hw he hwe h2, ih, map_add, map_smul, ← Module.End.mul_apply,
      ← pow_succ', ← Module.End.mul_apply (tieE w e) (tieE w e ^ j), ← pow_succ', add_assoc, ← add_smul]
    congr 2
    push_cast; ring

theorem Fpow_harm {u : MvPolynomial σ K} (hF : tieF w e u = 0) {t : ℕ} (ht : 1 ≤ t) :
    (tieF w e ^ t) u = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [add_comm, pow_succ, Module.End.mul_apply, hF, map_zero]

theorem fk_harm_Epow {g : MvPolynomial σ K} (hF : tieF w e g = 0) {t : ℕ} (ht : 1 ≤ t)
    (u : MvPolynomial σ K) : fk g ((tieE w e ^ t) u) = 0 := by
  rw [fk_symm, fk_E_pow, Fpow_harm hw he hwe hF ht, fk_zero_right]

theorem fk_EE (hr : 1 ≤ r) {a b a' b' : ℕ} {u u' : MvPolynomial σ K} (hu : BiHom w e a b u)
    (hF : tieF w e u = 0) (hu' : BiHom w e a' b' u') (hF' : tieF w e u' = 0) (i j : ℕ) :
    fk ((tieE w e ^ i) u) ((tieE w e ^ j) u') =
      if i = j then ((j.descFactorial j * (a' + b' + r - 1 + j).descFactorial j : ℕ) : K) * fk u u'
      else 0 := by
  have hN' : a' + b' + r = (a' + b' + r - 1) + 1 := by omega
  have hN : a + b + r = (a + b + r - 1) + 1 := by omega
  have P' := F_pow_E_pow hw he hwe u' a' b' _ (euler_w_of_biHom w e hu') (euler_e_of_biHom w e hu') hF' hN'
  have P := F_pow_E_pow hw he hwe u a b _ (euler_w_of_biHom w e hu) (euler_e_of_biHom w e hu) hF hN
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg (by omega), fk_E_pow, P', fk_smul_right, fk_harm_Epow hw he hwe hF (by omega), mul_zero]
  · rw [if_pos rfl, fk_E_pow, P', fk_smul_right, Nat.sub_self, pow_zero, Module.End.one_apply]
  · rw [if_neg (by omega), fk_symm, fk_E_pow, P, fk_smul_right, fk_harm_Epow hw he hwe hF' (by omega),
      mul_zero]

theorem fk_levels (hr : 1 ≤ r) (s : ℕ) (R : Finset ℕ) (u u' : ℕ → MvPolynomial σ K) (c d : ℕ → K)
    (α β α' β' : ℕ → ℕ) (hu : ∀ l ∈ R, BiHom w e (α l) (β l) (u l) ∧ tieF w e (u l) = 0)
    (hu' : ∀ l ∈ R, BiHom w e (α' l) (β' l) (u' l) ∧ tieF w e (u' l) = 0) :
    fk (∑ l ∈ R, c l • (tieE w e ^ (s + l)) (u l)) (∑ l ∈ R, d l • (tieE w e ^ (s + l)) (u' l)) =
      ∑ l ∈ R, c l * d l * (((s + l).descFactorial (s + l) *
        (α' l + β' l + r - 1 + (s + l)).descFactorial (s + l) : ℕ) : K) * fk (u l) (u' l) := by
  rw [fk_sum_left]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [fk_smul_left, fk_sum_right]
  have : ∀ l' ∈ R, fk ((tieE w e ^ (s + l)) (u l)) (d l' • (tieE w e ^ (s + l')) (u' l')) =
      if l = l' then d l' * ((((s + l').descFactorial (s + l') *
        (α' l' + β' l' + r - 1 + (s + l')).descFactorial (s + l') : ℕ) : K) * fk (u l) (u' l')) else 0 := by
    intro l' hl'
    rw [fk_smul_right, fk_EE hw he hwe hr (hu l hl).1 (hu l hl).2 (hu' l' hl').1 (hu' l' hl').2]
    by_cases h : l = l'
    · subst h; simp
    · rw [if_neg (by omega), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hl]
  ring

theorem decomp (hr : 1 ≤ r) : ∀ (a b : ℕ) (y : MvPolynomial σ K), BiHom w e a b y →
    ∃ u : ℕ → MvPolynomial σ K, y = ∑ l ∈ range (a + 1), (tieE w e ^ l) (u l) ∧
      ∀ l ∈ range (a + 1), tieF w e (u l) = 0 ∧ BiHom w e (a - l) (b - l) (u l) ∧ (u l ≠ 0 → l ≤ b) := by
  intro a
  induction a with
  | zero =>
    intro b y hy
    refine ⟨fun _ => y, by simp, fun l hl => ?_⟩
    have hl0 : l = 0 := by simp only [Finset.mem_range] at hl; omega
    subst hl0
    exact ⟨(biHom_F hw he hwe hy).2 (Or.inl rfl), by simpa using hy, fun _ => Nat.zero_le _⟩
  | succ a ih =>
    intro b y hy
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      refine ⟨fun l => if l = 0 then y else 0, ?_, fun l hl => ?_⟩
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro l _ hl; simp [hl]
        · simp
      · by_cases h : l = 0
        · subst h
          exact ⟨by simpa using (biHom_F hw he hwe hy).2 (Or.inr rfl), by simpa using hy, fun _ => le_rfl⟩
        · simp only [h, if_false]
          exact ⟨map_zero _, biHom_zero _ _, fun h' => absurd rfl h'⟩
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hFy := (biHom_F hw he hwe hy).1
      simp only [Nat.add_sub_cancel] at hFy
      obtain ⟨wl, hwl, hwc⟩ := ih b' _ hFy
      let κ : ℕ → ℕ := fun l => (l + 1) * ((a - l) + (b' - l) + r + l)
      have hκ : ∀ l, (κ l : K) ≠ 0 := fun l => by
        have : 0 < κ l := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast this.ne'
      let x := ∑ l ∈ range (a + 1), ((κ l : K))⁻¹ • (tieE w e ^ l) (wl l)
      have hFE : ∀ l ∈ range (a + 1), tieF w e ((tieE w e ^ (l + 1)) (wl l)) = (κ l : K) • (tieE w e ^ l) (wl l) := by
        intro l hl
        have hc := hwc l hl
        exact F_E_pow hw he hwe _ _ _ (euler_w_of_biHom w e hc.2.1) (euler_e_of_biHom w e hc.2.1) hc.1 l
      have hEx : tieE w e x = ∑ l ∈ range (a + 1), ((κ l : K))⁻¹ • (tieE w e ^ (l + 1)) (wl l) := by
        simp only [x, map_sum, map_smul]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [pow_succ', Module.End.mul_apply]
      have hFEx : tieF w e (tieE w e x) = tieF w e y := by
        rw [hEx, map_sum, hwl]
        refine Finset.sum_congr rfl (fun l hl => ?_)
        rw [map_smul, hFE l hl, smul_smul, inv_mul_cancel₀ (hκ l), one_smul]
      have hxB : BiHom w e a b' x := by
        apply biHom_sum
        intro l hl
        apply biHom_smul
        by_cases h0 : wl l = 0
        · rw [h0, map_zero]; exact biHom_zero _ _
        · have hc := hwc l hl
          have hlb := hc.2.2 h0
          have hla : l ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have := biHom_E_pow hw he hwe hc.2.1 l
          rwa [Nat.sub_add_cancel hla, Nat.sub_add_cancel hlb] at this
      refine ⟨fun l => if l = 0 then y - tieE w e x else ((κ (l - 1) : K))⁻¹ • wl (l - 1), ?_, fun l hl => ?_⟩
      · rw [Finset.sum_range_succ']
        simp only [if_true, pow_zero, Module.End.one_apply, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [hEx]
        have : ∀ l ∈ range (a + 1), (tieE w e ^ (l + 1)) (((κ l : K))⁻¹ • wl l) =
            ((κ l : K))⁻¹ • (tieE w e ^ (l + 1)) (wl l) := fun l _ => map_smul _ _ _
        rw [Finset.sum_congr rfl this]
        abel
      · by_cases h : l = 0
        · subst h
          simp only [if_true, Nat.sub_zero]
          refine ⟨by rw [map_sub, hFEx, sub_self], biHom_sub hy (biHom_E hw he hwe hxB), fun _ => Nat.zero_le _⟩
        · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
          simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          have hl' : l' ∈ range (a + 1) := by
            simp only [Finset.mem_range] at hl ⊢; omega
          have hc := hwc l' hl'
          refine ⟨by rw [map_smul, hc.1, smul_zero], ?_, fun h0 => ?_⟩
          · rw [Nat.add_sub_add_right, Nat.add_sub_add_right]; exact biHom_smul _ hc.2.1
          · have : wl l' ≠ 0 := fun h1 => h0 (by rw [h1, smul_zero])
            have := hc.2.2 this; omega

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open Finset

theorem ineq_core (A : ℕ) (δ Kc p0 : ℝ) (hδ : 0 < δ) (hKc : 0 ≤ Kc) (hp0 : 0 ≤ p0)
    (p nfv κ X X' Xc U U' Uc : ℕ → ℝ)
    (hX : ∀ l, 0 ≤ X l) (hX' : ∀ l, 0 ≤ X' l) (hU : ∀ l, 0 ≤ U l) (hU' : ∀ l, 0 ≤ U' l)
    (hXc : ∀ l, 2 * |Xc l| ≤ X l + X' l) (hUc : ∀ l, 2 * |Uc l| ≤ U l + U' l)
    (h0 : Uc 0 = Xc 0) (hnfv0 : nfv 0 = 1) (hpz : p 0 = p0) (hκ0 : κ 0 = 0)
    (hp : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ p l ∧ p l * δ ≤ Kc * nfv l)
    (hnfv : ∀ l, 1 ≤ l → l ≤ A → 0 ≤ nfv l ∧ nfv l * δ ≤ κ l * nfv l) :
    |∑ l ∈ range (A + 1), p l * Uc l - p0 * ∑ l ∈ range (A + 1), nfv l * Xc l| ≤
      (Kc * ∑ l ∈ range (A + 1), nfv l * (U l + U' l) +
        p0 * ∑ l ∈ range (A + 1), κ l * nfv l * (X l + X' l)) / (2 * δ) := by
  rw [le_div_iff₀ (by positivity)]
  simp only [Finset.sum_range_succ' _ A, hpz, h0, hnfv0, hκ0]
  have t1 : ∀ i ∈ range A, |p (i + 1) * Uc (i + 1)| * (2 * δ) ≤ Kc * (nfv (i + 1) * (U (i + 1) + U' (i + 1))) := by
    intro i hi
    have hiA : i + 1 ≤ A := by simp at hi; omega
    obtain ⟨hpn, hpb⟩ := hp (i + 1) (by omega) hiA
    have := mul_le_mul hpb (hUc (i + 1)) (by positivity) (by nlinarith [(hnfv (i+1) (by omega) hiA).1])
    rw [abs_mul, abs_of_nonneg hpn]
    nlinarith
  have t2 : ∀ i ∈ range A, |nfv (i + 1) * Xc (i + 1)| * (2 * δ) ≤ κ (i + 1) * nfv (i + 1) * (X (i + 1) + X' (i + 1)) := by
    intro i hi
    have hiA : i + 1 ≤ A := by simp at hi; omega
    obtain ⟨hn, hnb⟩ := hnfv (i + 1) (by omega) hiA
    have hκn : 0 ≤ κ (i + 1) * nfv (i + 1) := by nlinarith
    have := mul_le_mul hnb (hXc (i + 1)) (by positivity) hκn
    rw [abs_mul, abs_of_nonneg hn]
    nlinarith
  have s1 := Finset.sum_le_sum t1
  have s2 := Finset.sum_le_sum t2
  rw [← Finset.sum_mul] at s1 s2
  have a1 := Finset.abs_sum_le_sum_abs (fun i => p (i + 1) * Uc (i + 1)) (range A)
  have a2 := Finset.abs_sum_le_sum_abs (fun i => nfv (i + 1) * Xc (i + 1)) (range A)
  have e1 : ∑ i ∈ range A, p (i + 1) * Uc (i + 1) + p0 * Xc 0 -
      p0 * (∑ i ∈ range A, nfv (i + 1) * Xc (i + 1) + 1 * Xc 0) =
      ∑ i ∈ range A, p (i + 1) * Uc (i + 1) - p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1) := by ring
  rw [e1]
  have hpos1 : 0 ≤ Kc * (1 * (U 0 + U' 0)) := by have := hU 0; have := hU' 0; positivity
  have hsum_nn : 0 ≤ ∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc |∑ i ∈ range A, p (i + 1) * Uc (i + 1) - p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)| * (2 * δ)
      ≤ (|∑ i ∈ range A, p (i + 1) * Uc (i + 1)| + p0 * |∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)|) * (2 * δ) := by
        gcongr
        calc _ ≤ |∑ i ∈ range A, p (i + 1) * Uc (i + 1)| + |p0 * ∑ i ∈ range A, nfv (i + 1) * Xc (i + 1)| :=
              abs_sub _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg hp0]
    _ ≤ (∑ i ∈ range A, |p (i + 1) * Uc (i + 1)| + p0 * ∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)|) * (2 * δ) := by
        gcongr
    _ = (∑ i ∈ range A, |p (i + 1) * Uc (i + 1)|) * (2 * δ) +
          p0 * ((∑ i ∈ range A, |nfv (i + 1) * Xc (i + 1)|) * (2 * δ)) := by ring
    _ ≤ Kc * ∑ i ∈ range A, nfv (i + 1) * (U (i + 1) + U' (i + 1)) +
          p0 * ∑ i ∈ range A, κ (i + 1) * nfv (i + 1) * (X (i + 1) + X' (i + 1)) := by
        rw [Finset.mul_sum]
        exact add_le_add s1 (mul_le_mul_of_nonneg_left s2 hp0)
    _ ≤ _ := by
        rw [mul_add Kc, mul_add p0]
        simp only [zero_mul, add_zero]
        linarith
end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

noncomputable def kap0 (o n z t r : ℕ) : ℝ :=
  ((z + t).choose t : ℝ) / ((o + n + r + z - 1).choose t : ℝ) *
    ((t.factorial * (o + n + r - 1 - t).descFactorial t : ℕ) : ℝ)

noncomputable def Kc (o z : ℕ) : ℝ :=
  ∑ L ∈ range (o + 1), (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ)

theorem Kc_nonneg (o z : ℕ) : 0 ≤ Kc o z := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem kappa_zero_nonneg (o n z t r : ℕ) : 0 ≤ kap0 o n z t r := by
  unfold kap0; positivity

section
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe

theorem decompE {K : Type} [Field K] [CharZero K] (hr : 1 ≤ r) (A B : ℕ) (y : MvPolynomial σ K)
    (hy : BiHom w e (A - 1) (B - 1) y) (hy0 : y ≠ 0 → 1 ≤ A ∧ 1 ≤ B) :
    ∃ yl : ℕ → MvPolynomial σ K, tieE w e y = ∑ l ∈ range A, (tieE w e ^ (l + 1)) (yl l) ∧
      ∀ l ∈ range A, tieF w e (yl l) = 0 ∧ BiHom w e (A - 1 - l) (B - 1 - l) (yl l) := by
  by_cases h : y = 0
  · refine ⟨fun _ => 0, by simp [h], fun l _ => ⟨map_zero _, biHom_zero _ _⟩⟩
  · obtain ⟨hA, hB⟩ := hy0 h
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hy ⊢
    obtain ⟨yl, hyl, hc⟩ := decomp hw he hwe hr A' (B - 1) y hy
    refine ⟨yl, ?_, fun l hl => ⟨(hc l hl).1, (hc l hl).2.1⟩⟩
    rw [hyl, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [pow_succ', Module.End.mul_apply]

theorem core (hr : 1 ≤ r) (o n z t : ℕ) (ht : t ≤ o) (hon : o < n)
    (v0 y v0' y' : MvPolynomial σ ℝ)
    (hv0 : BiHom w e (o - t) (n - t) v0) (hy : BiHom w e (o - t - 1) (n - t - 1) y)
    (hy0 : y ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t)
    (hv0' : BiHom w e (o - t) (n - t) v0') (hy' : BiHom w e (o - t - 1) (n - t - 1) y')
    (hy0' : y' ≠ 0 → 1 ≤ o - t ∧ 1 ≤ n - t) :
    |fk (tiePhi w e o n z ((tieE w e ^ t) (v0 + tieE w e y))) ((tieE w e ^ t) (v0' + tieE w e y'))
        - kap0 o n z t r * fk v0 v0'| ≤
      (Kc o z * (fk (v0 + tieE w e y) (v0 + tieE w e y) + fk (v0' + tieE w e y') (v0' + tieE w e y')) +
        kap0 o n z t r * (fk (tieF w e v0) (tieF w e v0) + fk (tieF w e v0') (tieF w e v0'))) /
        (2 * ((n - o : ℕ) : ℝ)) := by
  set A := o - t with hAdef
  set Bn := n - t with hBdef
  have hAB : A ≤ Bn := by omega
  obtain ⟨x, hx, hxc⟩ := decomp hw he hwe hr A Bn v0 hv0
  obtain ⟨x', hx', hxc'⟩ := decomp hw he hwe hr A Bn v0' hv0'
  obtain ⟨yl, hyl, hylc⟩ := decompE hw he hwe hr A Bn y hy hy0
  obtain ⟨yl', hyl', hylc'⟩ := decompE hw he hwe hr A Bn y' hy' hy0'
  let u : ℕ → MvPolynomial σ ℝ := fun l => x l + (if l = 0 then 0 else yl (l - 1))
  let u' : ℕ → MvPolynomial σ ℝ := fun l => x' l + (if l = 0 then 0 else yl' (l - 1))

  have hsumE : ∀ (xx : ℕ → MvPolynomial σ ℝ) (yy : ℕ → MvPolynomial σ ℝ),
      ∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l + (if l = 0 then 0 else yy (l - 1))) =
        ∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l) + ∑ l ∈ range A, (tieE w e ^ (l + 1)) (yy l) := by
    intro xx yy
    simp only [map_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_range_succ']
    simp
  have hv : v0 + tieE w e y = ∑ l ∈ range (A + 1), (tieE w e ^ l) (u l) := by
    rw [hsumE, ← hx, ← hyl]
  have hv' : v0' + tieE w e y' = ∑ l ∈ range (A + 1), (tieE w e ^ l) (u' l) := by
    rw [hsumE, ← hx', ← hyl']
  have hucond : ∀ (xx yy : ℕ → MvPolynomial σ ℝ),
      (∀ l ∈ range (A + 1), tieF w e (xx l) = 0 ∧ BiHom w e (A - l) (Bn - l) (xx l) ∧ (xx l ≠ 0 → l ≤ Bn)) →
      (∀ l ∈ range A, tieF w e (yy l) = 0 ∧ BiHom w e (A - 1 - l) (Bn - 1 - l) (yy l)) →
      ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l + (if l = 0 then 0 else yy (l - 1))) ∧
        tieF w e (xx l + (if l = 0 then 0 else yy (l - 1))) = 0 := by
    intro xx yy hxx hyy l hl
    by_cases h0 : l = 0
    · subst h0; simpa using ⟨(hxx 0 hl).2.1, (hxx 0 hl).1⟩
    · have hl1 : l - 1 ∈ range A := by simp only [Finset.mem_range] at hl ⊢; omega
      simp only [h0, if_false]
      have hb := (hyy (l - 1) hl1).2
      rw [show A - 1 - (l - 1) = A - l by omega, show Bn - 1 - (l - 1) = Bn - l by omega] at hb
      exact ⟨biHom_add (hxx l hl).2.1 hb, by rw [map_add, (hxx l hl).1, (hyy (l - 1) hl1).1, add_zero]⟩
  have hu := hucond x yl hxc hylc
  have hu' := hucond x' yl' hxc' hylc'

  let c : ℕ → ℝ := fun l => ((z + (t + l)).choose (t + l) : ℝ) / ((o + n + r + z - 1).choose (t + l) : ℝ)
  have hphi : tiePhi w e o n z ((tieE w e ^ t) (v0 + tieE w e y)) =
      ∑ l ∈ range (A + 1), c l • (tieE w e ^ (t + l)) (u l) := by
    rw [hv, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hlA : l ≤ A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    rw [show (tieE w e ^ t) ((tieE w e ^ l) (u l)) = (tieE w e ^ (t + l)) (u l) by
      rw [pow_add, Module.End.mul_apply]]
    have hB := (hu l hl).1
    rw [show A - l = o - (t + l) by omega, show Bn - l = n - (t + l) by omega] at hB
    exact Formalism.GM.Top.levelAct ℝ σ r w e hw he hwe hr o n z (t + l) (u l) (by omega) (by omega) (hu l hl).2 hB
  have hEt : (tieE w e ^ t) (v0' + tieE w e y') =
      ∑ l ∈ range (A + 1), (fun _ => (1 : ℝ)) l • (tieE w e ^ (t + l)) (u' l) := by
    rw [hv', map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [one_smul, pow_add, Module.End.mul_apply]
  have hBform := fk_levels hw he hwe hr t (range (A + 1)) u u' c (fun _ => 1)
    (fun l => A - l) (fun l => Bn - l) (fun l => A - l) (fun l => Bn - l)
    (fun l hl => ⟨(hu l hl).1, (hu l hl).2⟩) (fun l hl => ⟨(hu' l hl).1, (hu' l hl).2⟩)

  have hlev0 : ∀ (uu uu' : ℕ → MvPolynomial σ ℝ),
      (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (uu l) ∧ tieF w e (uu l) = 0) →
      (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (uu' l) ∧ tieF w e (uu' l) = 0) →
      (cc : ℕ → ℝ) →
      fk (∑ l ∈ range (A + 1), cc l • (tieE w e ^ l) (uu l)) (∑ l ∈ range (A + 1), (tieE w e ^ l) (uu' l)) =
        ∑ l ∈ range (A + 1), cc l * 1 * (((0 + l).descFactorial (0 + l) *
          ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) * fk (uu l) (uu' l) := by
    intro uu uu' h1 h2 cc
    have := fk_levels hw he hwe hr 0 (range (A + 1)) uu uu' cc (fun _ => 1)
      (fun l => A - l) (fun l => Bn - l) (fun l => A - l) (fun l => Bn - l) h1 h2
    simpa using this
  have hxc2 : ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (x l) ∧ tieF w e (x l) = 0 :=
    fun l hl => ⟨(hxc l hl).2.1, (hxc l hl).1⟩
  have hxc2' : ∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (x' l) ∧ tieF w e (x' l) = 0 :=
    fun l hl => ⟨(hxc' l hl).2.1, (hxc' l hl).1⟩
  have h1s : ∀ (uu : ℕ → MvPolynomial σ ℝ),
      ∑ l ∈ range (A + 1), (tieE w e ^ l) (uu l) = ∑ l ∈ range (A + 1), (fun _ => (1 : ℝ)) l • (tieE w e ^ l) (uu l) := by
    intro uu; simp
  have hv0v0' := hlev0 x x' hxc2 hxc2' (fun _ => 1)
  rw [← h1s, ← hx, ← hx'] at hv0v0'
  have hvv := hlev0 u u hu hu (fun _ => 1)
  rw [← h1s, ← hv] at hvv
  have hvv' := hlev0 u' u' hu' hu' (fun _ => 1)
  rw [← h1s, ← hv'] at hvv'

  let κ : ℕ → ℕ := fun l => l * ((A - l) + (Bn - l) + r + (l - 1))
  have hEF : ∀ (xx : ℕ → MvPolynomial σ ℝ), (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l) ∧ tieF w e (xx l) = 0) →
      tieE w e (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) =
        ∑ l ∈ range (A + 1), ((κ l : ℕ) : ℝ) • (tieE w e ^ l) (xx l) := by
    intro xx hxx
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    by_cases h0 : l = 0
    · subst h0; simp [(hxx 0 hl).2, κ]
    · obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
      rw [F_E_pow hw he hwe _ _ _ (euler_w_of_biHom w e (hxx _ hl).1) (euler_e_of_biHom w e (hxx _ hl).1)
        (hxx _ hl).2 j, map_smul, ← Module.End.mul_apply, ← pow_succ']
      simp only [κ, Nat.add_sub_cancel]
  have hFF : ∀ (xx : ℕ → MvPolynomial σ ℝ), (∀ l ∈ range (A + 1), BiHom w e (A - l) (Bn - l) (xx l) ∧ tieF w e (xx l) = 0) →
      fk (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) (tieF w e (∑ l ∈ range (A + 1), (tieE w e ^ l) (xx l))) =
        ∑ l ∈ range (A + 1), ((κ l : ℕ) : ℝ) * 1 * (((0 + l).descFactorial (0 + l) *
          ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) * fk (xx l) (xx l) := by
    intro xx hxx
    rw [← fk_E, hEF xx hxx]
    exact hlev0 xx xx hxx hxx _
  have hF0 := hFF x hxc2
  rw [← hx] at hF0
  have hF0' := hFF x' hxc2'
  rw [← hx'] at hF0'

  rw [hphi, hEt, hBform, hv0v0', hvv, hvv', hF0, hF0']
  have hδ : (0 : ℝ) < ((n - o : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - o)
  have key := ineq_core A ((n - o : ℕ) : ℝ) (Kc o z) (kap0 o n z t r) hδ (Kc_nonneg o z) (kappa_zero_nonneg o n z t r)
    (fun l => c l * 1 * (((t + l).descFactorial (t + l) *
        ((A - l) + (Bn - l) + r - 1 + (t + l)).descFactorial (t + l) : ℕ) : ℝ))
    (fun l => 1 * 1 * (((0 + l).descFactorial (0 + l) * ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ))
    (fun l => ((κ l : ℕ) : ℝ))
    (fun l => fk (x l) (x l)) (fun l => fk (x' l) (x' l)) (fun l => fk (x l) (x' l))
    (fun l => fk (u l) (u l)) (fun l => fk (u' l) (u' l)) (fun l => fk (u l) (u' l))
    (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _) (fun l => fk_self_nonneg _)
    (fun l => fk_abs_le _ _) (fun l => fk_abs_le _ _)
    (by simp [u, u']) (by simp) ?_ (by simp [κ]) ?_ ?_
  · convert key using 2
    rw [mul_add, mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  · simp only [c, kap0, Nat.add_zero, Nat.sub_zero, Nat.descFactorial_self, mul_one]
    rw [show A + Bn + r - 1 + t = o + n + r - 1 - t by omega]
  · intro l hl1 hlA
    set L := t + l with hL
    have hLo : L ≤ o := by omega
    have hchpos : 0 < (o + n + r + z - 1).choose L := Nat.choose_pos (by omega)
    have hD : ((A - l) + (Bn - l) + r - 1 + L).descFactorial L ≤ L.factorial * (o + n + r + z - 1).choose L := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le _ (by omega)
    have hpl : c l * 1 * ((L.descFactorial L * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) ≤
        (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) := by
      simp only [c, mul_one, Nat.descFactorial_self]
      rw [← hL, div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hchpos)]
      have : ((L.factorial * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) ≤
          ((L.factorial * (L.factorial * (o + n + r + z - 1).choose L) : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left _ hD
      push_cast at this ⊢
      nlinarith [(Nat.cast_nonneg ((z + L).choose L) : (0:ℝ) ≤ _)]
    have hterm : (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) ≤ Kc o z := by
      unfold Kc
      exact Finset.single_le_sum (f := fun L => (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega))
    have hnf : ((n - o : ℕ) : ℝ) ≤ 1 * 1 * (((0 + l).descFactorial (0 + l) *
        ((A - l) + (Bn - l) + r - 1 + (0 + l)).descFactorial (0 + l) : ℕ) : ℝ) := by
      simp only [one_mul, zero_add, Nat.descFactorial_self]
      have h1 := Nat.pow_sub_le_descFactorial ((A - l) + (Bn - l) + r - 1 + l) l
      have h2 : n - o ≤ ((A - l) + (Bn - l) + r - 1 + l + 1 - l) := by omega
      have h3 : ((A - l) + (Bn - l) + r - 1 + l + 1 - l) ≤ ((A - l) + (Bn - l) + r - 1 + l + 1 - l) ^ l :=
        Nat.le_self_pow (by omega) _
      have h4 : 1 ≤ l.factorial := Nat.factorial_pos l
      have : n - o ≤ l.factorial * ((A - l) + (Bn - l) + r - 1 + l).descFactorial l :=
        le_trans (le_trans h2 (le_trans h3 h1)) (Nat.le_mul_of_pos_left _ h4)
      exact_mod_cast this
    have hpnn : 0 ≤ c l * 1 * ((L.descFactorial L * ((A - l) + (Bn - l) + r - 1 + L).descFactorial L : ℕ) : ℝ) := by
      simp only [c]; positivity
    refine ⟨hpnn, ?_⟩
    calc _ ≤ (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ) * ((n - o : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hpl hδ.le
      _ ≤ Kc o z * ((n - o : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hterm hδ.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hnf (Kc_nonneg o z)
  · intro l hl1 hlA
    refine ⟨by positivity, ?_⟩
    have hk : n - o ≤ κ l := by
      simp only [κ]
      have : n - o ≤ (A - l) + (Bn - l) + r + (l - 1) := by omega
      exact le_trans this (Nat.le_mul_of_pos_left _ (by omega))
    have hk' : ((n - o : ℕ) : ℝ) ≤ ((κ l : ℕ) : ℝ) := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_left hk' (by positivity) |>.trans_eq (by ring)

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section gen
variable (K : Type) [Field K]

noncomputable def fSub {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) :
    Fin N × Fin r → MvPolynomial (Fin (N + 1) × Fin r) K :=
  fun ⟨i, c⟩ =>
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c))

noncomputable def frz {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) K) : MvPolynomial (Fin (N + 1) × Fin r) K :=
  X (Fin.last N, ρ) ^ (n - LL.total) * aeval (fSub K LL ρ) f

noncomputable def gamK {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) K) : K :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : K) *
    fk (Formalism.GM.tiePhi (fun c : Fin r => (Fin.castSucc (Fin.last N), c)) (fun c : Fin r => (Fin.last (N + 1), c))
      ((LL.snoc n).deg (Fin.castSucc (Fin.last N))) ((LL.snoc n).deg (Fin.last (N + 1))) z
      (frz K LL ρ n f)) (frz K LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : K) * ∏ i, ((LL.deg i).factorial : K))

end gen

theorem fock_eq (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p F G = fk F G := by
  unfold M.fock fk; simp only [prod_eq_wf]

theorem freeze_eq (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.freeze p LL ρ n f = frz ℚ_[p] LL ρ n f := rfl

theorem tieGam_eq (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.tieGam p LL ρ z n f f' = gamK ℚ_[p] LL ρ z n f f' := by
  unfold M.tieGam gamK
  rw [fock_eq, freeze_eq, freeze_eq]
  rfl

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section bh
variable {K σ : Type} [Field K] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem biHom_one : BiHom w e 0 0 (1 : MvPolynomial σ K) := by
  classical
  intro m hm
  rw [show (1 : MvPolynomial σ K) = monomial 0 1 from rfl, support_monomial, if_neg one_ne_zero] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm; simp

theorem biHom_mul {a b a' b' : ℕ} {u v : MvPolynomial σ K} (hu : BiHom w e a b u) (hv : BiHom w e a' b' v) :
    BiHom w e (a + a') (b + b') (u * v) := by
  intro m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul u v hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  rw [(hu m1 hm1).1, (hu m1 hm1).2, (hv m2 hm2).1, (hv m2 hm2).2]
  exact ⟨rfl, rfl⟩

theorem biHom_pow {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) (k : ℕ) :
    BiHom w e (k * a) (k * b) (u ^ k) := by
  induction k with
  | zero => simpa using biHom_one
  | succ k ih =>
    rw [pow_succ, show (k + 1) * a = k * a + a by ring, show (k + 1) * b = k * b + b by ring]
    exact biHom_mul ih hu

theorem biHom_prod_pow {ι : Type} [DecidableEq ι] (t : Finset ι) (g : ι → MvPolynomial σ K) (A B k : ι → ℕ)
    (hg : ∀ i ∈ t, BiHom w e (A i) (B i) (g i)) :
    BiHom w e (∑ i ∈ t, k i * A i) (∑ i ∈ t, k i * B i) (∏ i ∈ t, g i ^ k i) := by
  induction t using Finset.induction_on with
  | empty => simpa using biHom_one
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.prod_insert hx]
    exact biHom_mul (biHom_pow (hg x (Finset.mem_insert_self _ _)) _)
      (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

theorem biHom_X_of (v : σ) {a b : ℕ} (ha : (∑ c, (Finsupp.single v 1 : σ →₀ ℕ) (w c)) = a)
    (hb : (∑ c, (Finsupp.single v 1 : σ →₀ ℕ) (e c)) = b) : BiHom w e a b (X v : MvPolynomial σ K) := by
  classical
  intro m hm
  rw [show (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) 1 from rfl, support_monomial,
    if_neg one_ne_zero] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm; exact ⟨ha, hb⟩

end bh

section frz
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

abbrev wW : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c)
abbrev eη : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c)

theorem wW_inj : Function.Injective (wW (N := N) (r := r)) := fun a b h => by simpa using h
theorem eη_inj : Function.Injective (eη (N := N) (r := r)) := fun a b h => by simpa using h
theorem wW_ne_eη : ∀ c d, (wW (N := N) (r := r)) c ≠ eη d := fun c d h => by
  simp only [Prod.mk.injEq] at h; exact Fin.castSucc_ne_last _ h.1

theorem biHom_Xcs (i : Fin (N + 1)) (c : Fin r) :
    BiHom (wW (N := N)) eη (if i = Fin.last N then 1 else 0) 0
      (X (Fin.castSucc i, c) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) := by
  apply biHom_X_of
  · simp only [Finsupp.single_apply, Prod.mk.injEq, Fin.castSucc_inj]
    by_cases h : i = Fin.last N
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp [Finsupp.single_apply, Fin.castSucc_ne_last]

theorem biHom_Xeta (c : Fin r) :
    BiHom (wW (N := N)) eη 0 1 (X (Fin.last (N + 1), c) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) := by
  apply biHom_X_of
  · simp [Finsupp.single_apply, (Fin.castSucc_ne_last _).symm]
  · simp [Finsupp.single_apply]

theorem biHom_fSub (x : Fin (N + 1) × Fin r) :
    BiHom (wW (N := N)) eη (if x.1 = Fin.last N then 1 else 0) 1 (fSub K LL ρ x) := by
  obtain ⟨i, c⟩ := x
  have hp : ∀ c1 c2, BiHom (wW (N := N)) eη (if i = Fin.last N then 1 else 0) 1
      ((X (Fin.last (N + 1), c1) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) * X (Fin.castSucc i, c2)) := by
    intro c1 c2
    have := biHom_mul (biHom_Xeta (K := K) (N := N) c1) (biHom_Xcs (K := K) i c2)
    simpa [add_comm] using this
  have hp' : ∀ c1 c2, BiHom (wW (N := N)) eη (if i = Fin.last N then 1 else 0) 1
      ((X (Fin.castSucc i, c2) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) * X (Fin.last (N + 1), c1)) := by
    intro c1 c2; rw [mul_comm]; exact hp c1 c2
  simp only [fSub]
  by_cases hv : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hv, if_pos hc]; exact biHom_sum _ _ (fun c' _ => hp' c' c')
  · rw [if_pos hv, if_neg hc]; exact hp ρ c
  · rw [if_neg hv, if_pos hc]; exact hp ρ ρ
  · rw [if_neg hv, if_neg hc]; exact biHom_sub (hp ρ c) (hp' c ρ)

theorem aeval_fSub_monomial (m : Fin (N + 1) × Fin r →₀ ℕ) :
    aeval (fSub K LL ρ) (monomial m (1 : K)) = ∏ x, fSub K LL ρ x ^ m x := by
  rw [aeval_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (by simp)

theorem prod_split {σ' : Type} [Fintype σ'] [DecidableEq σ'] {R : Type} [CommMonoid R] (g : σ' → R)
    (m : σ' →₀ ℕ) (x0 : σ') :
    ∏ x, g x ^ m x = g x0 ^ m x0 * ∏ x, g x ^ (Finsupp.update m x0 0) x := by
  have h : ∀ x, g x ^ m x = (if x = x0 then g x0 ^ m x0 else 1) * g x ^ (Finsupp.update m x0 0) x := by
    intro x
    by_cases hx : x = x0
    · subst hx; simp
    · simp [hx, Finsupp.update_apply]
  rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem fSub_alt (hv : LL.vec (Fin.last N) = true) :
    fSub K LL ρ (Fin.last N, ρ) = ∑ c, X (wW (N := N) c) * X (eη c) := by
  simp [fSub, hv]

theorem tieE_pow_eq (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) (a : ℕ) :
    (tieE (wW (N := N)) eη ^ a) g = (∑ c, X (wW (N := N) c) * X (eη c)) ^ a * g := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', Module.End.mul_apply, ih, tieE_apply', pow_succ', mul_assoc]

noncomputable def sq (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  ∏ x, fSub K LL ρ x ^ (Finsupp.update m (Fin.last N, ρ) 0) x

theorem frz_monomial (hv : LL.vec (Fin.last N) = true) (n : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    frz K LL ρ n (monomial m 1) =
      (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ))) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m) := by
  rw [frz, aeval_fSub_monomial, prod_split _ m (Fin.last N, ρ), fSub_alt LL ρ hv, tieE_pow_eq, sq]
  ring

end frz

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem sum_update {σ' : Type} [Fintype σ'] [DecidableEq σ'] (m : σ' →₀ ℕ) (x0 : σ') (g : σ' → ℕ) :
    ∑ x, m x * g x = ∑ x, (Finsupp.update m x0 0) x * g x + m x0 * g x0 := by
  have h : ∀ x, m x * g x = (Finsupp.update m x0 0) x * g x + (if x = x0 then m x0 * g x0 else 0) := by
    intro x; by_cases hx : x = x0
    · subst hx; simp
    · simp [hx, Finsupp.update_apply]
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem biHom_sq (m : Fin (N + 1) × Fin r →₀ ℕ) :
    BiHom (wW (N := N)) eη (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * (if x.1 = Fin.last N then 1 else 0))
      (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * 1) (sq (K := K) LL ρ m) :=
  biHom_prod_pow _ _ _ _ _ (fun x _ => biHom_fSub LL ρ x)

theorem multiDeg_total (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    ∑ x, m x * 1 = LL.total := by
  simp only [mul_one, M.Letters.total]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => hm i)

theorem multidegree_last_weight_sum (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    ∑ x, m x * (if x.1 = Fin.last N then 1 else 0) = LL.deg (Fin.last N) := by
  rw [Fintype.sum_prod_type, ← hm (Fin.last N)]
  rw [Finset.sum_eq_single (Fin.last N)]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem biHom_sq' (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - m (Fin.last N, ρ)) (LL.total - m (Fin.last N, ρ))
      (sq (K := K) LL ρ m) := by
  have h1 := sum_update m (Fin.last N, ρ) (fun x => if x.1 = Fin.last N then 1 else 0)
  have h2 := sum_update m (Fin.last N, ρ) (fun _ => 1)
  rw [multidegree_last_weight_sum LL m hm] at h1
  rw [multiDeg_total LL m hm] at h2
  simp only [if_true, mul_one] at h1 h2
  have := biHom_sq (K := K) LL ρ m
  simp only [mul_one] at this
  rwa [show ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * (if x.1 = Fin.last N then 1 else 0) =
      LL.deg (Fin.last N) - m (Fin.last N, ρ) by omega,
    show ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = LL.total - m (Fin.last N, ρ) by omega] at this

theorem pderiv_prod_zero {σ' ι : Type} [DecidableEq ι] (i : σ') (t : Finset ι) (g : ι → MvPolynomial σ' K)
    (k : ι → ℕ) (h : ∀ x ∈ t, k x = 0 ∨ pderiv i (g x) = 0) : pderiv i (∏ x ∈ t, g x ^ k x) = 0 := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih (fun x hx => h x (Finset.mem_insert_of_mem hx))]
    rcases h a (Finset.mem_insert_self _ _) with h0 | h0
    · simp [h0]
    · simp [Derivation.leibniz_pow, h0]

theorem pderiv_W_fSub (hv : LL.vec (Fin.last N) = true) (x : Fin (N + 1) × Fin r) (hx : x ≠ (Fin.last N, ρ)) :
    pderiv (wW (N := N) ρ) (fSub K LL ρ x) = 0 := by
  obtain ⟨i, c⟩ := x
  have hXcs : ∀ c', (i = Fin.last N → c' ≠ ρ) →
      pderiv (wW (N := N) ρ) (X (Fin.castSucc i, c') : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    intro c' hc'
    apply pderiv_X_of_ne
    intro h
    simp only [wW, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact hc' h.1 h.2
  have hXe : ∀ c', pderiv (wW (N := N) ρ) (X (Fin.last (N + 1), c') : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    intro c'; apply pderiv_X_of_ne
    intro h; simp only [wW, Prod.mk.injEq] at h; exact Fin.castSucc_ne_last _ h.1.symm
  simp only [fSub]
  by_cases hvi : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hvi, if_pos hc]
    have hi : i ≠ Fin.last N := fun h => hx (by rw [h, hc])
    rw [map_sum]; refine Finset.sum_eq_zero (fun c' _ => ?_)
    rw [Derivation.leibniz, hXcs c' (fun h => absurd h hi), hXe]; simp
  · rw [if_pos hvi, if_neg hc, Derivation.leibniz, hXcs c (fun _ => hc), hXe]; simp
  · have hi : i ≠ Fin.last N := fun h => hvi (h ▸ hv)
    rw [if_neg hvi, if_pos hc, Derivation.leibniz, hXcs ρ (fun h => absurd h hi), hXe]; simp
  · have hi : i ≠ Fin.last N := fun h => hvi (h ▸ hv)
    rw [if_neg hvi, if_neg hc, map_sub, Derivation.leibniz, Derivation.leibniz, hXcs c (fun h => absurd h hi),
      hXcs ρ (fun h => absurd h hi), hXe, hXe]; simp

theorem pderiv_W_sq (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    pderiv (wW (N := N) ρ) (sq (K := K) LL ρ m) = 0 := by
  apply pderiv_prod_zero
  intro x _
  by_cases hx : x = (Fin.last N, ρ)
  · left; subst hx; simp
  · right; exact pderiv_W_fSub LL ρ hv x hx

theorem F_eta_pow (k : ℕ) (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K)
    (hg : pderiv (wW (N := N) ρ) g = 0) :
    tieF (wW (N := N)) eη (X (Fin.last (N + 1), ρ) ^ k * g) = X (Fin.last (N + 1), ρ) ^ k * tieF (wW (N := N)) eη g := by
  rw [tieF_apply', tieF_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h1 : pderiv (wW (N := N) c) (X (Fin.last (N + 1), ρ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) = 0 := by
    apply pderiv_X_of_ne; intro h; simp only [wW, Prod.mk.injEq] at h; exact Fin.castSucc_ne_last _ h.1.symm
  by_cases hc : c = ρ
  · subst hc
    simp only [pderiv_mul, pderiv_pow, h1, hg, pderiv_X_self, mul_zero, zero_mul, add_zero, mul_one]
    simp [pderiv_mul, hg, h1]
  · rw [pderiv_mul, pderiv_pow, pderiv_X_of_ne (by simp [eη, Ne.symm hc] : (Fin.last (N + 1), ρ) ≠ eη (N := N) c)]
    simp [pderiv_mul, pderiv_pow, h1]

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section gen
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem wf_single_add (M : σ →₀ ℕ) (i : σ) (k : ℕ) :
    (wf (Finsupp.single i k + M) : K) = (((M i + k).descFactorial k : ℕ) : K) * wf M := by
  unfold wf
  have h : ∀ x : σ, ((((Finsupp.single i k + M : σ →₀ ℕ) x).factorial : ℕ) : K) =
      ((M x).factorial : K) * (if x = i then (((M i + k).descFactorial k : ℕ) : K) else 1) := by
    intro x
    by_cases hx : x = i
    · subst hx
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, if_true]
      have := Nat.factorial_mul_descFactorial (n := M x + k) (k := k) (by omega)
      rw [Nat.add_sub_cancel] at this
      rw [add_comm k, ← this]; push_cast; ring
    · simp [hx, Finsupp.single_apply, Ne.symm hx]
  rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp [mul_comm]

theorem fk_Xpow (i : σ) (k : ℕ) (g g' : MvPolynomial σ K) :
    fk (X i ^ k * g) (X i ^ k * g') =
      ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (((M i + k).descFactorial k : ℕ) : K) := by
  classical
  have hX : (X i ^ k : MvPolynomial σ K) = monomial (Finsupp.single i k) 1 := by rw [X_pow_eq_monomial]
  have hs : (X i ^ k * g).support ⊆ g.support.map (addLeftEmbedding (Finsupp.single i k)) := by
    intro M hM
    have := support_mul (X i ^ k) g hM
    rw [hX, support_monomial, if_neg one_ne_zero] at this
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp this
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
  rw [fk_eq_sum _ _ _ hs, Finset.sum_map]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  simp only [addLeftEmbedding_apply, hX, coeff_monomial_mul, one_mul, wf_single_add]
  ring

variable (P : σ → Prop) [DecidablePred P]

noncomputable def kill : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun v => if P v then (0 : MvPolynomial σ K) else X v)

theorem kill_monomial (M : σ →₀ ℕ) (a : K) :
    kill P (monomial M a) = if (∀ v, P v → M v = 0) then monomial M a else 0 := by
  unfold kill
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  split_ifs with h
  · rw [monomial_eq]
    congr 1
    refine Finsupp.prod_congr (fun v hv => ?_)
    have : ¬ P v := fun hp => (Finsupp.mem_support_iff.mp hv) (h v hp)
    rw [if_neg this]
  · push Not at h
    obtain ⟨v, hp, hv⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hv) (by rw [if_pos hp, zero_pow hv]),
      mul_zero]

theorem coeff_kill (g : MvPolynomial σ K) (M : σ →₀ ℕ) :
    coeff M (kill P g) = if (∀ v, P v → M v = 0) then coeff M g else 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial M' a =>
    rw [kill_monomial]
    by_cases hM : M' = M
    · subst hM; split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hM]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> ring

theorem kill_X (v : σ) : kill P (X v : MvPolynomial σ K) = if P v then 0 else X v := by
  unfold kill; rw [aeval_X]

end gen

section frz
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

def Pη (ρ : Fin r) (v : Fin (N + 1 + 1) × Fin r) : Prop := v.1 = Fin.last (N + 1) ∧ v.2 ≠ ρ

instance (ρ : Fin r) : DecidablePred (Pη (N := N) ρ) := fun v => by unfold Pη; infer_instance

def cs' : Fin (N + 1) × Fin r → Fin (N + 1 + 1) × Fin r := fun x => (Fin.castSucc x.1, x.2)

theorem cs'_inj : Function.Injective (cs' (N := N) (r := r)) := by
  intro a b h; simp only [cs', Prod.mk.injEq, Fin.castSucc_inj] at h; exact Prod.ext h.1 h.2

theorem kill_fSub (x : Fin (N + 1) × Fin r) :
    kill (K := K) (Pη ρ) (fSub K LL ρ x) = X (Fin.last (N + 1), ρ) * X (cs' x) := by
  obtain ⟨i, c⟩ := x
  have hcs : ∀ c', ¬ Pη (N := N) ρ (Fin.castSucc i, c') := fun c' h => Fin.castSucc_ne_last _ h.1
  have he : ∀ c', Pη (N := N) ρ (Fin.last (N + 1), c') ↔ c' ≠ ρ := fun c' => by simp [Pη]
  simp only [fSub, cs']
  by_cases hvi : LL.vec i = true <;> by_cases hc : c = ρ
  · rw [if_pos hvi, if_pos hc, map_sum]
    simp only [map_mul, kill_X, hcs, if_false, he, ite_not]
    rw [Finset.sum_eq_single ρ]
    · subst hc; simp [mul_comm]
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_pos hvi, if_neg hc]; simp only [map_mul, kill_X, hcs, he, if_false]; simp
  · rw [if_neg hvi, if_pos hc]; simp only [map_mul, kill_X, hcs, he, if_false]; subst hc; simp
  · rw [if_neg hvi, if_neg hc]; simp only [map_sub, map_mul, kill_X, hcs, he, if_false]; simp [hc]

theorem monomial_eq_prod {σ' : Type} [Fintype σ'] [DecidableEq σ'] (m : σ' →₀ ℕ) :
    (monomial m (1 : K) : MvPolynomial σ' K) = ∏ x, X x ^ m x := by
  rw [monomial_eq, C_1, one_mul]
  exact Finsupp.prod_fintype _ _ (by simp)

theorem kill_sq (m : Fin (N + 1) × Fin r →₀ ℕ) :
    kill (K := K) (Pη ρ) (sq LL ρ m) =
      X (Fin.last (N + 1), ρ) ^ (∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x) *
        monomial ((Finsupp.update m (Fin.last N, ρ) 0).mapDomain cs') 1 := by
  rw [sq, map_prod]
  simp only [map_pow, kill_fSub, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← rename_monomial, monomial_eq_prod, map_prod]
  simp [rename_X]

theorem wf_mapDomain (m : Fin (N + 1) × Fin r →₀ ℕ) :
    (wf (m.mapDomain (cs' (N := N))) : K) = wf m := by
  classical
  unfold wf
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map ⟨cs' (N := N), cs'_inj⟩))]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    simp [Finsupp.mapDomain_apply cs'_inj]
  · intro v _ hv
    have : v ∉ Set.range (cs' (N := N) (r := r)) := by
      rintro ⟨x, rfl⟩; exact hv (Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    rw [Finsupp.mapDomain_of_notMem_range _ _ this]; simp

theorem top_eq_kill (a d : ℕ) (g g' : MvPolynomial (Fin (N + 1 + 1) × Fin r) K)
    (hg : BiHom (wW (N := N)) eη a d g) :
    ∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M (Fin.last (N + 1), ρ) = d then 1 else 0) =
      fk (kill (Pη ρ) g) (kill (Pη ρ) g') := by
  have hs : (kill (K := K) (Pη ρ) g).support ⊆ g.support := by
    intro M hM
    rw [mem_support_iff, coeff_kill] at hM
    split_ifs at hM
    · exact mem_support_iff.mpr hM
    · exact absurd rfl hM
  rw [fk_eq_sum _ _ _ hs]
  refine Finset.sum_congr rfl (fun M hM => ?_)
  rw [coeff_kill, coeff_kill]
  have hd := (hg M hM).2
  have key : (∀ v, Pη (N := N) ρ v → M v = 0) ↔ M (Fin.last (N + 1), ρ) = d := by
    rw [← hd, ← Finset.add_sum_erase _ _ (Finset.mem_univ ρ)]
    constructor
    · intro h
      rw [Finset.sum_eq_zero (fun c hc => h _ ⟨rfl, Finset.ne_of_mem_erase hc⟩), add_zero]
    · intro h v hv
      obtain ⟨v1, v2⟩ := v
      simp only [Pη] at hv
      obtain ⟨rfl, hv2⟩ := hv
      have h0 : ∑ c ∈ Finset.univ.erase ρ, M (eη (N := N) c) = 0 := by simp only [eη] at h ⊢; omega
      exact (Finset.sum_eq_zero_iff.mp h0) v2 (Finset.mem_erase.mpr ⟨hv2, Finset.mem_univ _⟩)
  by_cases h : M (Fin.last (N + 1), ρ) = d
  · rw [if_pos (key.mpr h), if_pos (key.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (key.mp h')), if_neg h]; ring

end frz

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open Filter Topology Finset

theorem tendsto_lin (b : ℝ) : Tendsto (fun n : ℕ => ((n : ℝ) + b) / n) atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat b).const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

theorem choose_lim (c s j : ℕ) :
    Tendsto (fun n : ℕ => ((n + c - s).choose j : ℝ) / (n : ℝ) ^ j) atTop (𝓝 (1 / (j.factorial : ℝ))) := by
  have hprod : Tendsto (fun n : ℕ => ∏ i ∈ range j, (((n : ℝ) + ((c : ℝ) - s - i)) / n)) atTop (𝓝 1) := by
    have := tendsto_finsetProd (range j) (fun i _ => tendsto_lin ((c : ℝ) - s - i))
    simpa using this
  have h2 := hprod.div_const (j.factorial : ℝ)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (s + j + 1)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hd := Nat.descFactorial_eq_factorial_mul_choose (n + c - s) j
  rw [Nat.descFactorial_eq_prod_range] at hd
  have hcast : ((∏ i ∈ range j, (n + c - s - i) : ℕ) : ℝ) = ∏ i ∈ range j, ((n : ℝ) + ((c : ℝ) - s - i)) := by
    push_cast
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < j := Finset.mem_range.mp hi
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hC : ((n + c - s).choose j : ℝ) = (∏ i ∈ range j, ((n : ℝ) + ((c : ℝ) - s - i))) / j.factorial := by
    rw [← hcast, hd]; push_cast; field_simp
  rw [hC, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  field_simp

theorem inv_pow_lim (t : ℕ) (ht : 1 ≤ t) : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ t) atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow t
  rw [zero_pow (by omega)] at h
  refine h.congr' ?_
  filter_upwards with n
  rw [div_pow, one_pow]

theorem choose_lim' (S j d : ℕ) (hjd : j ≤ d) :
    Tendsto (fun n : ℕ => ((n + j - S).choose j : ℝ) / (n : ℝ) ^ d) atTop
      (𝓝 (if j = d then 1 / (d.factorial : ℝ) else 0)) := by
  by_cases h : j = d
  · subst h; rw [if_pos rfl]; exact choose_lim j S j
  · rw [if_neg h]
    have h1 := (choose_lim j S j).mul (inv_pow_lim (d - j) (by omega))
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [show d = j + (d - j) by omega, pow_add]
    field_simp
    rw [Nat.add_sub_cancel_left]

theorem coeff_of_tendsto (R : Polynomial ℝ) (D : ℕ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => R.eval (n : ℝ) / (n : ℝ) ^ D) atTop (𝓝 L)) : R.coeff D = L := by
  set Q : Polynomial ℝ := Polynomial.X ^ D with hQ
  have hQe : ∀ x : ℝ, Q.eval x = x ^ D := fun x => by simp [hQ]
  have hQd : Q.degree = D := by simp [hQ]
  have hQl : Q.leadingCoeff = 1 := by simp [hQ]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  rcases lt_trichotomy R.degree Q.degree with hlt | heq | hgt
  · have h0 := (Polynomial.div_tendsto_atTop_zero_of_degree_lt R Q hlt).comp hnat
    simp only [Function.comp_def, hQe] at h0
    have hL := tendsto_nhds_unique h h0
    rw [hL]
    exact Polynomial.coeff_eq_zero_of_degree_lt (by rw [← hQd]; exact hlt)
  · have h0 := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq R Q heq).comp hnat
    simp only [Function.comp_def, hQe, hQl, div_one] at h0
    have hL := tendsto_nhds_unique h h0
    rw [hL, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some (heq.trans hQd)]
  · exfalso
    have hR0 : R ≠ 0 := fun h0 => by rw [h0, Polynomial.degree_zero] at hgt; exact absurd hgt (by simp)
    have hlc : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hR0
    rcases lt_or_gt_of_ne hlc with hneg | hpos
    · have h0 := (Polynomial.div_tendsto_atBot_of_degree_gt' R Q hgt (by rw [hQl, div_one]; exact hneg)).comp hnat
      simp only [Function.comp_def, hQe] at h0
      exact not_tendsto_nhds_of_tendsto_atBot h0 L h
    · have h0 := (Polynomial.div_tendsto_atTop_of_degree_gt' R Q hgt (by rw [hQl, div_one]; exact hpos)).comp hnat
      simp only [Function.comp_def, hQe] at h0
      exact not_tendsto_nhds_of_tendsto_atTop h0 L h

theorem fk_eta_lim {σ : Type} [Fintype σ] [DecidableEq σ] (i : σ) (S d : ℕ) (g g' : MvPolynomial σ ℝ)
    (hg : ∀ M ∈ g.support, M i ≤ d) :
    Tendsto (fun n : ℕ => fk (MvPolynomial.X i ^ (n - S) * g) (MvPolynomial.X i ^ (n - S) * g') /
        (((n - S).factorial : ℝ) * (n : ℝ) ^ d)) atTop
      (𝓝 (∑ M ∈ g.support, g.coeff M * g'.coeff M * wf M * (if M i = d then 1 / (d.factorial : ℝ) else 0))) := by
  have hlim : ∀ M ∈ g.support, Tendsto (fun n : ℕ => g.coeff M * g'.coeff M * wf M *
      (((n + M i - S).choose (M i) : ℝ) / (n : ℝ) ^ d)) atTop
      (𝓝 (g.coeff M * g'.coeff M * wf M * (if M i = d then 1 / (d.factorial : ℝ) else 0))) :=
    fun M hM => (choose_lim' S (M i) d (hg M hM)).const_mul _
  refine (tendsto_finsetSum _ hlim).congr' ?_
  filter_upwards [eventually_ge_atTop (S + 1)] with n hn
  rw [fk_Xpow, Finset.sum_div]
  refine Finset.sum_congr rfl (fun M _ => ?_)
  have hk : (n - S).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hc := Nat.descFactorial_eq_factorial_mul_choose (M i + (n - S)) (n - S)
  rw [← Nat.choose_symm_add, show M i + (n - S) = n + M i - S by omega] at hc
  rw [show M i + (n - S) = n + M i - S by omega, hc]
  push_cast
  have hk' : ((n - S).factorial : ℝ) ≠ 0 := by exact_mod_cast hk
  have hn0 : (n : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  field_simp

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)

theorem snoc_degree_last_weight (n : ℕ) : (LL.snoc n).deg (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) := by
  simp [M.Letters.snoc]

theorem snoc_deg_eta (n : ℕ) : (LL.snoc n).deg (Fin.last (N + 1)) = n := by
  simp [M.Letters.snoc]

noncomputable def V0 (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m else 0

noncomputable def Yh (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then 0
  else (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ) - e - 1)) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m)

noncomputable def gv (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ) - e)) (sq LL ρ m)

noncomputable def gF (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then tieF (wW (N := N)) eη (sq LL ρ m) else 0

theorem E_pow_X_mul (j k : ℕ) (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) :
    (tieE (wW (N := N)) eη ^ j) (X (Fin.last (N + 1), ρ) ^ k * g) =
      X (Fin.last (N + 1), ρ) ^ k * (tieE (wW (N := N)) eη ^ j) g := by
  rw [tieE_pow_eq, tieE_pow_eq]; ring

theorem leading_vector_add_linked (m : Fin (N + 1) × Fin r →₀ ℕ) (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) :
    V0 (K := K) LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n) =
      X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m := by
  unfold V0 Yh gv
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h, if_pos h, h, Nat.sub_self, pow_zero, Module.End.one_apply, map_zero, add_zero]
  · rw [if_neg h, if_neg h, zero_add, ← Module.End.mul_apply, ← pow_succ',
      show m (Fin.last N, ρ) - e - 1 + 1 = m (Fin.last N, ρ) - e by omega, E_pow_X_mul]

theorem frz_shape (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) :
    frz K LL ρ n (monomial m 1) =
      (tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n)) := by
  rw [frz_monomial LL ρ hv, leading_vector_add_linked LL ρ e m hme, gv, ← E_pow_X_mul, ← Module.End.mul_apply, ← pow_add,
    Nat.add_sub_cancel' hme]

theorem linked_map_leading_vector (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) :
    tieF (wW (N := N)) eη (V0 (K := K) LL ρ e m n) = X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gF LL ρ e m := by
  unfold V0 gF
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h, if_pos h, F_eta_pow ρ _ _ (pderiv_W_sq LL ρ hv m)]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

theorem m_W_le (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    m (Fin.last N, ρ) ≤ LL.deg (Fin.last N) := by
  rw [← hm (Fin.last N)]
  exact Finset.single_le_sum (f := fun c => m (Fin.last N, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)

theorem o_le_S : LL.deg (Fin.last N) ≤ LL.total :=
  Finset.single_le_sum (f := LL.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

theorem biHom_Xsq (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (n : ℕ) (hn : LL.total ≤ n) :
    BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - m (Fin.last N, ρ)) (n - m (Fin.last N, ρ))
      (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq (K := K) LL ρ m) := by
  have h1 := biHom_pow (biHom_Xeta (K := K) (N := N) ρ) (n - LL.total)
  have h2 := biHom_mul h1 (biHom_sq' (K := K) LL ρ m hm)
  have hS := m_W_le LL ρ m hm
  have hoS := o_le_S LL
  rwa [mul_zero, zero_add, mul_one, show n - LL.total + (LL.total - m (Fin.last N, ρ)) = n - m (Fin.last N, ρ) by omega]
    at h2

variable (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m)
  (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) (hn : LL.total ≤ n)
include hm hme hn

theorem bihomogeneous_leading_vector : BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - e) (n - e) (V0 (K := K) LL ρ e m n) := by
  unfold V0
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h]; have := biHom_Xsq (K := K) LL ρ m hm n hn; rwa [h] at this
  · rw [if_neg h]; exact biHom_zero _ _

theorem biHom_Yh : BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - e - 1) (n - e - 1) (Yh (K := K) LL ρ e m n) := by
  unfold Yh
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h]; exact biHom_zero _ _
  · rw [if_neg h]
    have := biHom_E_pow wW_inj eη_inj wW_ne_eη (biHom_Xsq (K := K) LL ρ m hm n hn) (m (Fin.last N, ρ) - e - 1)
    have hS := m_W_le LL ρ m hm
    have hoS := o_le_S LL
    rwa [show LL.deg (Fin.last N) - m (Fin.last N, ρ) + (m (Fin.last N, ρ) - e - 1) = LL.deg (Fin.last N) - e - 1 by omega,
      show n - m (Fin.last N, ρ) + (m (Fin.last N, ρ) - e - 1) = n - e - 1 by omega] at this

theorem Yh_ne : Yh (K := K) LL ρ e m n ≠ 0 → 1 ≤ LL.deg (Fin.last N) - e ∧ 1 ≤ n - e := by
  intro h
  unfold Yh at h
  by_cases h' : m (Fin.last N, ρ) = e
  · rw [if_pos h'] at h; exact absurd rfl h
  · have hS := m_W_le LL ρ m hm
    have hoS := o_le_S LL
    omega

omit hn in
theorem gv_eta_le : ∀ M ∈ (gv (K := K) LL ρ e m).support, M (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro M hM
  have hb := biHom_E_pow wW_inj eη_inj wW_ne_eη (biHom_sq' (K := K) LL ρ m hm) (m (Fin.last N, ρ) - e)
  have h2 := (hb M hM).2
  have hS := m_W_le LL ρ m hm
  have hoS := o_le_S LL
  have h3 : M (Fin.last (N + 1), ρ) ≤ ∑ c, M (eη (N := N) c) :=
    Finset.single_le_sum (f := fun c => M (eη (N := N) c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
  simp only [eη] at h2 h3
  omega

omit hn in
theorem gF_eta_le : ∀ M ∈ (gF (K := K) LL ρ e m).support, M (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro M hM
  unfold gF at hM
  by_cases h : m (Fin.last N, ρ) = e
  · rw [if_pos h] at hM
    have hb := (biHom_F wW_inj eη_inj wW_ne_eη (biHom_sq' (K := K) LL ρ m hm)).1
    have h2 := (hb M hM).2
    have h3 : M (Fin.last (N + 1), ρ) ≤ ∑ c, M (eη (N := N) c) :=
      Finset.single_le_sum (f := fun c => M (eη (N := N) c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
    simp only [eη] at h2 h3
    omega
  · rw [if_neg h] at hM; simp at hM

omit hn hme in
theorem sq_eta_le (he : m (Fin.last N, ρ) = e) : ∀ M ∈ (sq (K := K) LL ρ m).support, M (Fin.last (N + 1), ρ) ≤ LL.total - e := by
  intro M hM
  have h2 := (biHom_sq' (K := K) LL ρ m hm M hM).2
  have h3 : M (Fin.last (N + 1), ρ) ≤ ∑ c, M (eη (N := N) c) :=
    Finset.single_le_sum (f := fun c => M (eη (N := N) c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
  simp only [eη] at h2 h3
  omega

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM Filter Topology

theorem kappa_zero_tendsto_factorials (o z e r : ℕ) :
    Tendsto (fun n : ℕ => kap0 o n z e r) atTop (𝓝 (((z + e).choose e : ℝ) * e.factorial * e.factorial)) := by
  have h1 := choose_lim (o + r) (1 + e) e
  have h2 := choose_lim (o + r + z) 1 e
  have hf : (1 / (e.factorial : ℝ)) ≠ 0 := by
    have : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero e
    simpa using this
  have h3 := ((h1.div h2 hf).const_mul (((z + e).choose e : ℝ) * e.factorial * e.factorial))
  rw [div_self hf, mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (e + 1)] with n hn
  have hn0 : (n : ℝ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n ≠ 0))
  unfold kap0
  rw [show o + n + r - 1 - e = n + (o + r) - (1 + e) by omega, show o + n + r + z - 1 = n + (o + r + z) - 1 by omega,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hc : (((n + (o + r + z) - 1).choose e : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  simp only [Pi.div_apply]
  push_cast
  field_simp

theorem chooseA_lim (o z r : ℕ) :
    Tendsto (fun n : ℕ => ((o + n + r + z - 1).choose o : ℝ) / (n : ℝ) ^ o) atTop (𝓝 (1 / (o.factorial : ℝ))) := by
  refine (choose_lim (o + r + z) 1 o).congr' (Eventually.of_forall (fun n => ?_))
  simp only
  rw [show n + (o + r + z) - 1 = o + n + r + z - 1 by omega]

theorem inv_sub_lim (o : ℕ) : Tendsto (fun n : ℕ => 1 / (2 * ((n - o : ℕ) : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n - o : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat o)
  have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (1 / 2 : ℝ)
  rw [mul_zero] at h2
  refine h2.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp_apply]
  field_simp

section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]

theorem fk_monomial (M M' : σ →₀ ℕ) :
    fk (monomial M (1 : K)) (monomial M' 1) = if M = M' then wf M else 0 := by
  classical
  unfold fk
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : M = M'
  · subst h; simp
  · have h2 : ¬ M' = M := fun h' => h h'.symm
    simp [h, h2]

end

section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

noncomputable def inMono (e : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then monomial m 1 else 0

theorem wf_split (m : Fin (N + 1) × Fin r →₀ ℕ) :
    (wf m : K) = ((m (Fin.last N, ρ)).factorial : K) * wf (Finsupp.update m (Fin.last N, ρ) 0) := by
  unfold wf
  have h2 : ∀ x : Fin (N + 1) × Fin r, ((m x).factorial : K) =
      (if x = (Fin.last N, ρ) then ((m (Fin.last N, ρ)).factorial : K) else 1) *
        (((Finsupp.update m (Fin.last N, ρ) 0) x).factorial : K) := by
    intro x; by_cases hx : x = (Fin.last N, ρ)
    · subst hx; simp
    · simp [hx, Finsupp.update_apply]
  rw [Finset.prod_congr rfl (fun x _ => h2 x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem update_eq_iff (m m' : Fin (N + 1) × Fin r →₀ ℕ) (h : m (Fin.last N, ρ) = m' (Fin.last N, ρ)) :
    Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0 ↔ m = m' := by
  constructor
  · intro hu
    ext x
    by_cases hx : x = (Fin.last N, ρ)
    · subst hx; exact h
    · have := congrArg (fun f => f x) hu
      simpa [Finsupp.update_apply, hx] using this
  · intro h'; rw [h']

theorem fk_kill_sq (m m' : Fin (N + 1) × Fin r →₀ ℕ) (d : ℕ)
    (hd : ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = d) (hd' : ∑ x, (Finsupp.update m' (Fin.last N, ρ) 0) x = d) :
    fk (kill (K := K) (Pη ρ) (sq LL ρ m)) (kill (Pη ρ) (sq LL ρ m')) =
      if Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0 then
        (d.factorial : K) * wf (Finsupp.update m (Fin.last N, ρ) 0) else 0 := by
  classical
  rw [kill_sq, kill_sq, hd, hd', fk_Xpow, support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
    coeff_monomial, if_pos rfl, coeff_monomial, wf_mapDomain]
  have h0 : ((Finsupp.update m (Fin.last N, ρ) 0).mapDomain (cs' (N := N))) (Fin.last (N + 1), ρ) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    simp only [cs', Prod.mk.injEq] at hx
    exact Fin.castSucc_ne_last _ hx.1
  rw [h0, zero_add, Nat.descFactorial_self]
  by_cases h : Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0
  · rw [h]; simp; ring
  · have h'' : ¬ ((Finsupp.update m' (Fin.last N, ρ) 0).mapDomain (cs' (N := N)) =
        (Finsupp.update m (Fin.last N, ρ) 0).mapDomain (cs' (N := N))) :=
      fun h' => h (Finsupp.mapDomain_injective cs'_inj h').symm
    rw [if_neg h'', if_neg h]; ring

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM Filter Topology

section
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem sum_update_eq (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = LL.total - m (Fin.last N, ρ) := by
  have h2 := sum_update m (Fin.last N, ρ) (fun _ => 1)
  rw [multiDeg_total LL m hm] at h2
  simp only [mul_one] at h2
  omega

theorem limit_value (z e : ℕ) (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m') :
    (1 / ((LL.deg (Fin.last N)).factorial : ℝ)) *
      (((z + e).choose e : ℝ) * e.factorial * e.factorial *
        (if m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e then
          ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
            (if M (Fin.last (N + 1), ρ) = LL.total - e then 1 / ((LL.total - e).factorial : ℝ) else 0)
        else 0) + 0) /
      (((LL.total).factorial : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) =
    (((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
      ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) := by
  have ho : ((LL.deg (Fin.last N)).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hS : ((LL.total).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hd : ((LL.total - e).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hpr : (∏ i, ((LL.deg i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast Nat.factorial_ne_zero _)
  by_cases h : m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e
  · rw [if_pos h]
    have hT : ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
        (if M (Fin.last (N + 1), ρ) = LL.total - e then 1 / ((LL.total - e).factorial : ℝ) else 0) =
        fk (kill (K := ℝ) (Pη ρ) (sq LL ρ m)) (kill (Pη ρ) (sq LL ρ m')) / ((LL.total - e).factorial : ℝ) := by
      have hb := biHom_sq' (K := ℝ) LL ρ m hm
      rw [h.1] at hb
      rw [← top_eq_kill ρ _ _ _ _ hb, Finset.sum_div]
      refine Finset.sum_congr rfl (fun M _ => ?_)
      split_ifs <;> ring
    rw [hT, fk_kill_sq LL ρ m m' (LL.total - e) (by rw [sum_update_eq LL ρ m hm, h.1])
      (by rw [sum_update_eq LL ρ m' hm', h.2])]
    unfold inMono
    rw [if_pos h.1, if_pos h.2, fk_monomial, wf_split ρ m, h.1]
    by_cases hq : Finsupp.update m (Fin.last N, ρ) 0 = Finsupp.update m' (Fin.last N, ρ) 0
    · rw [if_pos hq, if_pos ((update_eq_iff ρ m m' (h.1.trans h.2.symm)).mp hq)]
      push_cast
      field_simp
      ring
    · rw [if_neg hq, if_neg (fun h' => hq ((update_eq_iff ρ m m' (h.1.trans h.2.symm)).mpr h'))]
      simp
  · rw [if_neg h]
    have : fk (inMono (K := ℝ) ρ e m) (inMono ρ e m') = 0 := by
      unfold inMono
      by_cases h1 : m (Fin.last N, ρ) = e
      · rw [if_neg (fun h2 => h ⟨h1, h2⟩), fk_zero_right]
      · rw [if_neg h1, fk_zero_left]
    rw [this]; simp

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM Filter Topology

section
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)

theorem real_mono (hr : 1 ≤ r) (hv : LL.vec (Fin.last N) = true) (z e : ℕ)
    (m m' : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) (hm' : M.MultiDeg LL m')
    (hme : e ≤ m (Fin.last N, ρ)) (hme' : e ≤ m' (Fin.last N, ρ)) :
    Tendsto (fun n : ℕ => gamK ℝ LL ρ z n (monomial m 1) (monomial m' 1) /
        (n : ℝ) ^ (LL.total + LL.deg (Fin.last N) - e)) atTop
      (𝓝 ((((e.factorial * (z + e).choose e : ℕ) : ℝ) * fk (inMono (K := ℝ) ρ e m) (inMono ρ e m')) /
        ((((LL.deg (Fin.last N)).factorial * LL.total.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)))) := by
  have heo : e ≤ LL.deg (Fin.last N) := le_trans hme (m_W_le LL ρ m hm)
  have hoS : LL.deg (Fin.last N) ≤ LL.total := o_le_S LL
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  set P : ℝ := ((S.factorial : ℕ) : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ) with hP
  have hPpos : 0 < P := by
    have : 0 < ∏ i, ((LL.deg i).factorial : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast Nat.factorial_pos _)
    have h2 : (0 : ℝ) < ((S.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity

  let Bf : ℕ → ℝ := fun n => fk (tiePhi (wW (N := N)) eη o n z
      ((tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m n + tieE (wW (N := N)) eη (Yh LL ρ e m n))))
      ((tieE (wW (N := N)) eη ^ e) (V0 LL ρ e m' n + tieE (wW (N := N)) eη (Yh LL ρ e m' n)))
  have hgam : ∀ n, gamK ℝ LL ρ z n (monomial m 1) (monomial m' 1) =
      ((o + n + r + z - 1).choose o : ℝ) * Bf n / ((((n - S).factorial : ℕ) : ℝ) * P) := by
    intro n
    unfold gamK
    rw [snoc_degree_last_weight, snoc_deg_eta, frz_shape LL ρ e hv m hme, frz_shape LL ρ e hv m' hme']
    simp only [Bf, hP]
    push_cast
    ring

  let Q : ℕ → ℝ := fun n => (((n - S).factorial : ℕ) : ℝ) * (n : ℝ) ^ (S - e)
  let i0 : Fin (N + 1 + 1) × Fin r := (Fin.last (N + 1), ρ)
  have hX1 := fk_eta_lim i0 S (S - e) (gv LL ρ e m) (gv LL ρ e m) (gv_eta_le (K := ℝ) LL ρ e m hm hme)
  have hX2 := fk_eta_lim i0 S (S - e) (gv LL ρ e m') (gv LL ρ e m') (gv_eta_le (K := ℝ) LL ρ e m' hm' hme')
  have hY1 := fk_eta_lim i0 S (S - e) (gF LL ρ e m) (gF LL ρ e m) (gF_eta_le (K := ℝ) LL ρ e m hm hme)
  have hY2 := fk_eta_lim i0 S (S - e) (gF LL ρ e m') (gF LL ρ e m') (gF_eta_le (K := ℝ) LL ρ e m' hm' hme')
  set T : ℝ := if m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e then
          ∑ M ∈ (sq (K := ℝ) LL ρ m).support, (sq LL ρ m).coeff M * (sq LL ρ m').coeff M * wf M *
            (if M (Fin.last (N + 1), ρ) = S - e then 1 / ((S - e).factorial : ℝ) else 0)
        else 0 with hT
  have hf3 : Tendsto (fun n => fk (V0 (K := ℝ) LL ρ e m n) (V0 LL ρ e m' n) / Q n) atTop (𝓝 T) := by
    by_cases h : m (Fin.last N, ρ) = e ∧ m' (Fin.last N, ρ) = e
    · rw [hT, if_pos h]
      have := fk_eta_lim i0 S (S - e) (sq (K := ℝ) LL ρ m) (sq (K := ℝ) LL ρ m') (sq_eta_le (K := ℝ) LL ρ e m hm h.1)
      refine this.congr' (Eventually.of_forall (fun n => ?_))
      simp only [V0, if_pos h.1, if_pos h.2, Q, i0]
      rfl
    · rw [hT, if_neg h]
      refine tendsto_const_nhds.congr' (Eventually.of_forall (fun n => ?_))
      simp only [V0]
      by_cases h1 : m (Fin.last N, ρ) = e
      · rw [if_neg (fun h2 => h ⟨h1, h2⟩), fk_zero_right, zero_div]
      · rw [if_neg h1, fk_zero_left, zero_div]

  let f4 : ℕ → ℝ := fun n => (Bf n - kap0 o n z e r * fk (V0 LL ρ e m n) (V0 LL ρ e m' n)) / Q n
  let bd : ℕ → ℝ := fun n =>
    (Kc o z * (fk (X i0 ^ (n - S) * gv LL ρ e m) (X i0 ^ (n - S) * gv LL ρ e m) / Q n +
        fk (X i0 ^ (n - S) * gv LL ρ e m') (X i0 ^ (n - S) * gv LL ρ e m') / Q n) +
      kap0 o n z e r * (fk (X i0 ^ (n - S) * gF LL ρ e m) (X i0 ^ (n - S) * gF LL ρ e m) / Q n +
        fk (X i0 ^ (n - S) * gF LL ρ e m') (X i0 ^ (n - S) * gF LL ρ e m') / Q n)) *
      (1 / (2 * ((n - o : ℕ) : ℝ)))
  have hbd : Tendsto bd atTop (𝓝 0) := by
    have := (((hX1.add hX2).const_mul (Kc o z)).add ((kappa_zero_tendsto_factorials o z e r).mul (hY1.add hY2))).mul (inv_sub_lim o)
    rw [mul_zero] at this
    exact this
  have hf4 : Tendsto f4 atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [eventually_ge_atTop (S + 1)] with n hn
    have hon : o < n := by omega
    have hc := core wW_inj eη_inj wW_ne_eη hr o n z e heo hon (V0 (K := ℝ) LL ρ e m n) (Yh LL ρ e m n)
      (V0 LL ρ e m' n) (Yh LL ρ e m' n)
      (bihomogeneous_leading_vector LL ρ e m hm hme n (by omega)) (biHom_Yh LL ρ e m hm hme n (by omega)) (Yh_ne LL ρ e m hm hme n (by omega))
      (bihomogeneous_leading_vector LL ρ e m' hm' hme' n (by omega)) (biHom_Yh LL ρ e m' hm' hme' n (by omega))
      (Yh_ne LL ρ e m' hm' hme' n (by omega))
    rw [leading_vector_add_linked LL ρ e m hme, leading_vector_add_linked LL ρ e m' hme', linked_map_leading_vector LL ρ e hv m, linked_map_leading_vector LL ρ e hv m'] at hc
    have hBf : Bf n = fk (tiePhi (wW (N := N)) eη o n z ((tieE (wW (N := N)) eη ^ e)
        (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m)))
        ((tieE (wW (N := N)) eη ^ e) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * gv LL ρ e m')) := by
      simp only [Bf]; rw [leading_vector_add_linked LL ρ e m hme, leading_vector_add_linked LL ρ e m' hme']
    have hQ : 0 < Q n := by
      have : (0 : ℝ) < (((n - S).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have h2 : (0 : ℝ) < (n : ℝ) ^ (S - e) := pow_pos (by exact_mod_cast (by omega : 0 < n)) _
      positivity
    have hδ : (0 : ℝ) < ((n - o : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - o)
    rw [Real.norm_eq_abs]
    simp only [f4, bd, abs_div, abs_of_pos hQ]
    rw [hBf, div_le_iff₀ hQ]
    refine le_trans hc (le_of_eq ?_)
    simp only [i0]
    field_simp
    rfl

  have hmain := ((chooseA_lim o z r).mul (((kappa_zero_tendsto_factorials o z e r).mul hf3).add hf4)).div_const P
  rw [← limit_value LL ρ z e m m' hm hm']
  have hlim_eq : 1 / ((o.factorial : ℕ) : ℝ) * (((z + e).choose e : ℝ) * e.factorial * e.factorial * T + 0) / P =
      1 / (o.factorial : ℝ) * (((z + e).choose e : ℝ) * e.factorial * e.factorial * T + 0) /
        (((LL.total).factorial : ℝ) * ∏ i, ((LL.deg i).factorial : ℝ)) := by
    simp only [hP]
    rfl
  rw [← hlim_eq]
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (S + 1)] with n hn
  rw [hgam n]
  have hQ0 : (((n - S).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [f4, Q]
  rw [show S + o - e = o + (S - e) by omega, pow_add]
  field_simp
  ring

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable (K : Type) [Field K] [CharZero K]

local notation "ι" => algebraMap ℚ K

theorem map_fSub {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (x : Fin N × Fin r) :
    map ι (fSub ℚ LL ρ x) = fSub K LL ρ x := by
  obtain ⟨i, c⟩ := x
  simp only [fSub]
  split_ifs <;> simp

theorem map_frz_monomial {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ) (m : Fin N × Fin r →₀ ℕ) :
    map ι (frz ℚ LL ρ n (monomial m 1)) = frz K LL ρ n (monomial m 1) := by
  simp only [frz, aeval_monomial, map_one, one_mul, Finsupp.prod, map_mul, map_pow, map_X, map_prod, map_fSub]

variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem map_tieE (g : MvPolynomial σ ℚ) : map ι (tieE w e g) = tieE w e (map ι g) := by
  simp [tieE_apply', map_mul, map_sum, map_X]

theorem map_tieF (g : MvPolynomial σ ℚ) : map ι (tieF w e g) = tieF w e (map ι g) := by
  simp [tieF_apply', map_sum, pderiv_map]

theorem map_tieE_pow (j : ℕ) (g : MvPolynomial σ ℚ) :
    map ι ((tieE w e ^ j) g) = (tieE w e ^ j) (map ι g) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, map_tieE, ih, pow_succ', Module.End.mul_apply]

theorem map_tieF_pow (j : ℕ) (g : MvPolynomial σ ℚ) :
    map ι ((tieF w e ^ j) g) = (tieF w e ^ j) (map ι g) := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, map_tieF, ih, pow_succ', Module.End.mul_apply]

theorem map_smul' (c : ℚ) (g : MvPolynomial σ ℚ) : map ι (c • g) = (ι c) • map ι g := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_tiePhi (o n z : ℕ) (g : MvPolynomial σ ℚ) :
    map ι (tiePhi w e o n z g) = tiePhi w e o n z (map ι g) := by
  unfold tiePhi
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul', map_tieE_pow, map_tieF_pow]
  congr 1
  simp [map_div₀]

theorem map_wf (m : σ →₀ ℕ) : ι (wf m) = (wf m : K) := by
  simp [wf, map_prod]

theorem fk_map (F G : MvPolynomial σ ℚ) : fk (map ι F) (map ι G) = ι (fk F G) := by
  unfold fk
  rw [support_map_of_injective _ (algebraMap ℚ K).injective, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [coeff_map, coeff_map, map_mul, map_mul, map_wf]

theorem gamK_map {N : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ) (m m' : Fin (N + 1) × Fin r →₀ ℕ) :
    gamK K LL ρ z n (monomial m 1) (monomial m' 1) = ι (gamK ℚ LL ρ z n (monomial m 1) (monomial m' 1)) := by
  unfold gamK
  rw [← map_frz_monomial K LL ρ n m, ← map_frz_monomial K LL ρ n m', ← map_tiePhi, fk_map]
  simp [map_div₀, map_prod]

theorem inMono_map {N : ℕ} (ρ : Fin r) (e : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) :
    map ι (inMono (K := ℚ) ρ e m) = inMono (K := K) ρ e m := by
  unfold inMono; split_ifs <;> simp

end

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM.leadingTermLemmas

open MvPolynomial Finset Formalism.GM

section
variable {K : Type} [Field K]

theorem as_sum_smul {σ : Type} (f : MvPolynomial σ K) :
    f = ∑ m ∈ f.support, f.coeff m • monomial m (1 : K) := by
  conv_lhs => rw [f.as_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_monomial, smul_eq_mul, mul_one]

theorem frz_sum {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) K) :
    frz K LL ρ n f = ∑ m ∈ f.support, f.coeff m • frz K LL ρ n (monomial m 1) := by
  conv_lhs => rw [as_sum_smul f]
  simp only [frz, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]

theorem gamK_bil {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) K) :
    gamK K LL ρ z n f f' = ∑ m ∈ f.support, ∑ m' ∈ f'.support,
      f.coeff m * f'.coeff m' * gamK K LL ρ z n (monomial m 1) (monomial m' 1) := by
  unfold gamK
  rw [frz_sum LL ρ n f, frz_sum LL ρ n f', map_sum, fk_sum_left]
  simp only [map_smul, fk_smul_left, fk_sum_right, fk_smul_right, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
  ring

end

theorem initPart_sum (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) (e : ℕ)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.initPart (Fin.last N, ρ) e f = ∑ m ∈ f.support, f.coeff m • inMono (K := ℚ_[p]) ρ e m := by
  unfold M.initPart inMono
  refine Finset.sum_congr rfl (fun m _ => ?_)
  split_ifs <;> simp [smul_monomial]

theorem fock_init_bil (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) (e : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.fock p (M.initPart (Fin.last N, ρ) e f) (M.initPart (Fin.last N, ρ) e f') =
      ∑ m ∈ f.support, ∑ m' ∈ f'.support, f.coeff m * f'.coeff m' * fk (inMono (K := ℚ_[p]) ρ e m) (inMono ρ e m') := by
  rw [fock_eq, initPart_sum, initPart_sum, fk_sum_left]
  simp only [fk_smul_left, fk_sum_right, fk_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
  ring

end Formalism.GM.leadingTermLemmas

namespace Formalism.GM

open MvPolynomial Finset Filter Topology Formalism.GM.leadingTermLemmas

theorem gamma_leading_term : M.GamLead := by
  intro p _ N r LL ρ z e f f' P hr hv hf hf' hof hof' hP
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  set D := S + o - e with hD
  set I := f.support ×ˢ f'.support with hI
  set c : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℚ_[p] :=
    fun i => f.coeff i.1 * f'.coeff i.2 with hc
  set γ : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℕ → ℚ :=
    fun i n => gamK ℚ LL ρ z n (monomial i.1 1) (monomial i.2 1) with hγ
  set Lq : (Fin (N + 1) × Fin r →₀ ℕ) × (Fin (N + 1) × Fin r →₀ ℕ) → ℚ :=
    fun i => ((e.factorial * (z + e).choose e : ℕ) : ℚ) * fk (inMono (K := ℚ) ρ e i.1) (inMono ρ e i.2) /
      (((o.factorial * S.factorial : ℕ) : ℚ) * ∏ j, ((LL.deg j).factorial : ℚ)) with hLq
  have hexp : ∀ n, M.tieGam p LL ρ z n f f' = ∑ i ∈ I, c i * algebraMap ℚ ℚ_[p] (γ i n) := by
    intro n
    rw [tieGam_eq, gamK_bil, Finset.sum_product]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
    rw [gamK_map ℚ_[p]]
  have htgt : ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
      M.fock p (M.initPart (Fin.last N, ρ) e f) (M.initPart (Fin.last N, ρ) e f') /
      (((o.factorial * S.factorial : ℕ) : ℚ_[p]) * ∏ j, ((LL.deg j).factorial : ℚ_[p])) =
      ∑ i ∈ I, c i * algebraMap ℚ ℚ_[p] (Lq i) := by
    rw [fock_init_bil, Finset.mul_sum, Finset.sum_div, Finset.sum_product]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m' _ => ?_)
    rw [← inMono_map ℚ_[p], ← inMono_map ℚ_[p], fk_map]
    simp only [hLq, hc, map_div₀, map_mul, map_natCast, map_prod]
    ring
  rw [htgt, ← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp (fun ψ => ?_)
  have hψ : ∀ (a : ℚ_[p]) (q : ℚ), ψ (a * algebraMap ℚ ℚ_[p] q) = q * ψ a := by
    intro a q
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

  set Rψ : Polynomial ℚ := ∑ k ∈ range (P.natDegree + 1), Polynomial.C (ψ (P.coeff k)) * Polynomial.X ^ k with hR
  have hRcoeff : ∀ k, Rψ.coeff k = ψ (P.coeff k) := by
    intro k
    rw [hR, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have : P.natDegree < k := by simp at hk; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, map_zero]
  have hReval : ∀ q : ℚ, Rψ.eval q = ψ (P.eval (algebraMap ℚ ℚ_[p] q)) := by
    intro q
    rw [Polynomial.eval_eq_sum_range (p := P), map_sum, hR, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, hψ]
    ring
  have hRn : ∀ n : ℕ, S ≤ n → Rψ.eval (n : ℚ) = ∑ i ∈ I, γ i n * ψ (c i) := by
    intro n hn
    rw [hReval, map_natCast, ← hP n hn, hexp, map_sum]
    exact Finset.sum_congr rfl (fun i _ => hψ _ _)

  have hmem : ∀ i ∈ I, M.MultiDeg LL i.1 ∧ M.MultiDeg LL i.2 ∧ e ≤ i.1 (Fin.last N, ρ) ∧ e ≤ i.2 (Fin.last N, ρ) := by
    intro i hi
    rw [hI, Finset.mem_product] at hi
    have h1 := (MvPolynomial.mem_restrictSupport_iff _).mp hf hi.1
    have h2 := (MvPolynomial.mem_restrictSupport_iff _).mp hf' hi.2
    exact ⟨h1, h2, hof.1 _ hi.1, hof'.1 _ hi.2⟩
  set Rr : Polynomial ℝ := Rψ.map (algebraMap ℚ ℝ) with hRr
  have hlim : Tendsto (fun n : ℕ => Rr.eval (n : ℝ) / (n : ℝ) ^ D) atTop
      (𝓝 (∑ i ∈ I, (algebraMap ℚ ℝ (Lq i)) * ψ (c i))) := by
    have each : ∀ i ∈ I, Tendsto (fun n : ℕ => gamK ℝ LL ρ z n (monomial i.1 1) (monomial i.2 1) / (n : ℝ) ^ D *
        ψ (c i)) atTop (𝓝 ((algebraMap ℚ ℝ (Lq i)) * ψ (c i))) := by
      intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hmem i hi
      have := (real_mono LL ρ hr hv z e i.1 i.2 h1 h2 h3 h4).mul_const (ψ (c i) : ℝ)
      convert this using 2
      rw [hLq]
      simp only
      rw [← inMono_map ℝ ρ e i.1, ← inMono_map ℝ ρ e i.2, fk_map ℝ]
      simp only [map_div₀, map_mul, map_natCast, map_prod, eq_ratCast]
      rfl
    refine (tendsto_finsetSum I each).congr' ?_
    filter_upwards [eventually_ge_atTop S] with n hn
    rw [hRr, Polynomial.eval_natCast_map, hRn n hn, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [gamK_map ℝ]
    simp only [hγ, eq_ratCast]
    push_cast
    ring
  have hcoef := coeff_of_tendsto Rr D _ hlim
  rw [hRr, Polynomial.coeff_map, hRcoeff] at hcoef
  have hq : ψ (P.coeff D) = ∑ i ∈ I, Lq i * ψ (c i) := by
    apply (algebraMap ℚ ℝ).injective
    rw [hcoef, map_sum (algebraMap ℚ ℝ)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [eq_ratCast]
    push_cast
    ring
  rw [map_sub, hq, map_sum]
  rw [sub_eq_zero]
  exact Finset.sum_congr rfl (fun i _ => (hψ _ _).symm)

end Formalism.GM
