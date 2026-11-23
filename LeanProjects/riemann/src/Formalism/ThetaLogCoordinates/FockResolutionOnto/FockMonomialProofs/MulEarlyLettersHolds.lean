import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementB
import Formalism.PolynomialDimension.MultinomialDepth.PartnerM

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

noncomputable abbrev SuppLE [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}

noncomputable abbrev wd [NeZero r] (LL : Letters N) (j : ℕ) (l : List (Fin r)) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (l.map fun c => glAct p LL j 0 c).prod

theorem wd_nil [NeZero r] (LL : Letters N) (j : ℕ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j [] F = F := rfl

theorem wd_cons [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (l : List (Fin r))
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j (c :: l) F = glAct p LL j 0 c (wd p LL j l F) := by
  simp only [wd, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem wd_snoc [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (l : List (Fin r))
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    wd p LL j (l ++ [c]) F = wd p LL j l (glAct p LL j 0 c F) := by
  simp only [wd, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, Module.End.mul_apply]

private theorem single_add_sub_single_eq_of_one_le {σ : Type} (m : σ →₀ ℕ) (v : σ) (hv : 1 ≤ m v) :
    Finsupp.single v 1 + (m - Finsupp.single v 1) = m :=
  add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hv)

private theorem wt_single_add_eq (LL : Letters N) (j : ℕ) (c' : Fin r) (i : Fin N) (c : Fin r)
    (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c' (Finsupp.single (i, c) 1 + m) = wt LL j c' m +
      (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (if c = c' then 1 else 0) := by
  classical
  unfold wt
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · by_cases hc : c = c'
    · subst hc
      by_cases hi : (i : ℕ) < j
      · cases hv : LL.vec i <;> simp [hi, hv] <;> ring
      · simp [hi]
    · have h0 : (Finsupp.single (i, c) 1 : Fin N × Fin r →₀ ℕ) (i, c') = 0 := by
        simp [Finsupp.single_apply, hc]
      simp [h0, hc]
  · intro k _ hk
    have h0 : (Finsupp.single (i, c) 1 : Fin N × Fin r →₀ ℕ) (k, c') = 0 := by
      simp [Finsupp.single_apply, Ne.symm hk]
    simp [h0]
  · simp

theorem low_keep [NeZero r] (LL : Letters N) (j : ℕ) (a b : Fin r) (ha : a ≠ 0) (M : WithTop ℤ) :
    ∀ x ∈ SuppLE p LL j M, glAct p LL j a b x ∈ SuppLE p LL j M := by
  intro x hx
  refine glAct_keep (p := p) LL j a b _ _ ?_ ?_ x hx
  · intro i hi hv m hm h1
    have hm' := single_add_sub_single_eq_of_one_le m (i, b) h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [← hm'] at hm
    rw [wt_single_add_eq] at hm ⊢
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    simp [hi, hv, ha] <;> split_ifs <;> omega
  · intro i hi hv m hm h1
    have hm' := single_add_sub_single_eq_of_one_le m (i, a) h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [← hm'] at hm
    rw [wt_single_add_eq] at hm ⊢
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    simp [hi, hv, ha] <;> split_ifs <;> omega

theorem word_low [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (l : List (Fin r)) :
    ∀ a b : Fin r, a ≠ 0 → ∀ G : MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ l', wd p LL j l' G ∈ SuppLE p LL j M) → wd p LL j l (glAct p LL j a b G) ∈ SuppLE p LL j M := by
  induction l using List.reverseRecOn with
  | nil =>
    intro a b ha G hG
    rw [wd_nil]
    exact low_keep p LL j a b ha M G (by simpa [wd_nil] using hG [])
  | append_singleton l c ih =>
    intro a b ha G hG
    rw [wd_snoc]
    have hc := glAct_comm (p := p) LL j 0 c a b G
    have heq : glAct p LL j 0 c (glAct p LL j a b G) = glAct p LL j a b (glAct p LL j 0 c G) +
        ((if c = a then glAct p LL j 0 b G else 0) - (if b = 0 then glAct p LL j a c G else 0)) := by
      rw [← hc]; abel
    rw [heq, map_add, map_sub]
    refine Submodule.add_mem _ ?_ (Submodule.sub_mem _ ?_ ?_)
    · exact ih a b ha _ (fun l' => by rw [← wd_snoc]; exact hG _)
    · split_ifs
      · rw [← wd_snoc]; exact hG _
      · rw [map_zero]; exact Submodule.zero_mem _
    · split_ifs
      · exact ih a c ha G hG
      · rw [map_zero]; exact Submodule.zero_mem _

end Gen

theorem raising_criterion_holds : FirstCoordinateRaisingCriterion := by
  intro p hp N r hr LL j M F
  constructor
  · intro hF l
    have hy : ∀ l : List (Fin r), ((l.map fun c => glAct p LL j 0 c).prod) F ∈ YCond p LL j M := by
      intro l
      induction l with
      | nil => simpa using hF
      | cons c l ih =>
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
        exact ycond_glStable (p := p) LL j M 0 c _ ih
    exact ycond_le_supp (p := p) LL j M (hy l)
  · intro hF
    have hS : F ∈ ⨅ l : List (Fin r), (SuppLE p LL j M).comap (wd p LL j l) :=
      (Submodule.mem_iInf _).mpr fun l => hF l
    have hle : (⨅ l : List (Fin r), (SuppLE p LL j M).comap (wd p LL j l)) ≤ YCond p LL j M := by
      unfold YCond
      refine le_sSup ⟨?_, ?_⟩
      · intro x hx
        have := (Submodule.mem_iInf _).mp hx []
        rw [Submodule.mem_comap, wd_nil] at this
        exact this
      · intro c d x hx
        rw [Submodule.mem_iInf] at hx ⊢
        intro l
        rw [Submodule.mem_comap]
        by_cases hc : c = 0
        · subst hc; rw [← wd_snoc]; exact hx _
        · exact word_low p LL j M l c d hc x (fun l' => hx l')
    exact hle hS

section Tools

variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem glAct_mul (LL : Letters N) (j : ℕ) (a b : Fin r) (f g : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glAct p LL j a b (f * g) = glAct p LL j a b f * g + f * glAct p LL j a b g := by
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring

theorem glAct_X (LL : Letters N) (j : ℕ) (a b c : Fin r) (i : Fin N) :
    glAct p LL j a b (X (i, c)) =
      if (i : ℕ) < j then (if LL.vec i then (if b = c then X (i, a) else 0) else (if a = c then -X (i, b) else 0))
      else 0 := by
  classical
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < j
    · cases hv : LL.vec i
      · by_cases hac : a = c
        · subst hac; simp [hi, hv, pderiv_X]
        · simp [hi, hv, pderiv_X, Pi.single_apply, hac, Ne.symm hac]
      · by_cases hbc : b = c
        · subst hbc; simp [hi, hv, pderiv_X]
        · simp [hi, hv, pderiv_X, Pi.single_apply, hbc, Ne.symm hbc]
    · simp [hi]
  · intro k _ hk
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hk, hk]
  · simp

theorem X_mul_mem {σ : Type} (v : σ) (Q : Set (σ →₀ ℕ)) (g : MvPolynomial σ ℚ_[p]) :
    X v * g ∈ restrictSupport ℚ_[p] Q ↔ g ∈ restrictSupport ℚ_[p] {m | Finsupp.single v 1 + m ∈ Q} := by
  rw [mem_restrictSupport_iff, mem_restrictSupport_iff, support_X_mul, Finset.coe_map,
    Set.image_subset_iff]
  exact Iff.rfl

theorem wt_single_add (LL : Letters N) (j : ℕ) (c' : Fin r) (i : Fin N) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c' (Finsupp.single (i, c) 1 + m) = wt LL j c' m +
      (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (if c = c' then 1 else 0) := by
  exact wt_single_add_eq LL j c' i c m

theorem abs_wt_le (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    |wt LL j c m| ≤ ((∑ v, m v : ℕ) : ℤ) := by
  unfold wt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun i : Fin N => ((m (i, c) : ℕ) : ℤ)) fun i _ => ?_).trans ?_
  · split_ifs <;> simp
  · calc ∑ i : Fin N, ((m (i, c) : ℕ) : ℤ) ≤ ∑ i : Fin N, ∑ c' : Fin r, ((m (i, c') : ℕ) : ℤ) :=
          Finset.sum_le_sum fun i _ =>
            Finset.single_le_sum (f := fun c' => ((m (i, c') : ℕ) : ℤ)) (fun _ _ => by positivity)
              (Finset.mem_univ c)
      _ = ((∑ v, m v : ℕ) : ℤ) := by simp [Fintype.sum_prod_type]

theorem sum_shift {σ : Type} [Fintype σ] [DecidableEq σ] (m : σ →₀ ℕ) (u v : σ) (hv : 1 ≤ m v) :
    ∑ w, (Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ) w = ∑ w, m w := by
  have h := single_add_sub_single_eq_of_one_le m v hv
  have e1 : ∀ x : σ, ∑ w, (Finsupp.single x 1 : σ →₀ ℕ) w = 1 := by
    intro x; simp [Finsupp.single_apply]
  calc ∑ w, (Finsupp.single u 1 + (m - Finsupp.single v 1) : σ →₀ ℕ) w
      = ∑ w, (Finsupp.single u 1 : σ →₀ ℕ) w + ∑ w, (m - Finsupp.single v 1 : σ →₀ ℕ) w := by
        simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    _ = ∑ w, (Finsupp.single v 1 : σ →₀ ℕ) w + ∑ w, (m - Finsupp.single v 1 : σ →₀ ℕ) w := by rw [e1, e1]
    _ = ∑ w, m w := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => by rw [← Finsupp.add_apply, h]

private theorem sum_weight_mul_single_add_eq {σ : Type} [Fintype σ] (w : σ → ℕ) (u : σ) (m : σ →₀ ℕ) :
    ∑ v, w v * (Finsupp.single u 1 + m : σ →₀ ℕ) v = w u + ∑ v, w v * m v := by
  classical
  simp [Finsupp.single_apply, mul_add, Finset.sum_add_distrib]

theorem raise_nil [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : ∃ n : ℕ, ((glAct p LL j 0 c) ^ n) h = 0 := by
  classical
  let wg : Fin N × Fin r → ℕ := fun v => if (v.1 : ℕ) < j then
      (if LL.vec v.1 then (if v.2 = c then 1 else 0) else (if v.2 = 0 then 1 else 0)) else 0
  let φ : (Fin N × Fin r →₀ ℕ) → ℕ := fun m => ∑ v, wg v * m v
  have step : ∀ k : ℕ, ∀ x ∈ restrictSupport ℚ_[p] {m | φ m < k + 1},
      glAct p LL j 0 c x ∈ restrictSupport ℚ_[p] {m | φ m < k} := by
    intro k
    refine glAct_keep (p := p) LL j 0 c _ _ ?_ ?_
    · intro i hi hv m hm h1
      have hm' := single_add_sub_single_eq_of_one_le m (i, c) h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [← hm'] at hm
      simp only [φ, sum_weight_mul_single_add_eq] at hm ⊢
      have e0 : wg (i, 0) = 0 := by simp [wg, hi, hv, Ne.symm hc]
      have e1 : wg (i, c) = 1 := by simp [wg, hi, hv]
      omega
    · intro i hi hv m hm h1
      have hm' := single_add_sub_single_eq_of_one_le m (i, 0) h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [← hm'] at hm
      simp only [φ, sum_weight_mul_single_add_eq] at hm ⊢
      have e0 : wg (i, c) = 0 := by simp [wg, hi, hv, hc]
      have e1 : wg (i, 0) = 1 := by simp [wg, hi, hv]
      omega
  have iter : ∀ n k : ℕ, ∀ x ∈ restrictSupport ℚ_[p] {m | φ m < n + k},
      ((glAct p LL j 0 c) ^ n) x ∈ restrictSupport ℚ_[p] {m | φ m < k} := by
    intro n
    induction n with
    | zero => intro k x hx; simpa using hx
    | succ n ih =>
      intro k x hx
      rw [pow_succ, Module.End.mul_apply]
      exact ih k _ (step (n + k) x (by rw [show n + k + 1 = n + 1 + k by omega]; exact hx))
  refine ⟨h.support.sup φ + 1, ?_⟩
  have h0 := iter (h.support.sup φ + 1) 0 h (by
    rw [mem_restrictSupport_iff]
    intro m hm
    simp only [Set.mem_setOf_eq, add_zero]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := φ) (Finset.mem_coe.mp hm)))
  rw [mem_restrictSupport_iff] at h0
  apply MvPolynomial.support_eq_empty.mp
  by_contra hne
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have := h0 (Finset.mem_coe.mpr hm)
  simp at this

theorem withTop_shift (w : ℤ) (M : WithTop ℤ) :
    ((w + 1 : ℤ) : WithTop ℤ) ≤ M ↔ ((w : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ) := by
  induction M using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    omega

end Tools

theorem mul_early_letters_holds : MulEarly := by
  intro p hp K r hr LL j M c h hj
  have hK : ¬ K < j := by omega
  have hX : ∀ a b : Fin r, ∀ g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j a b (X (Fin.last K, c) * g) = X (Fin.last K, c) * glAct p LL j a b g := by
    intro a b g
    rw [glAct_mul, glAct_X]
    simp [Fin.val_last, hK]
  have hw : ∀ l : List (Fin r),
      wd p LL j l (X (Fin.last K, c) * h) = X (Fin.last K, c) * wd p LL j l h := by
    intro l
    induction l with
    | nil => simp only [wd_nil]
    | cons d l ih => rw [wd_cons, wd_cons, ih, hX]
  rw [raising_criterion_holds p (K + 1) r LL j M, raising_criterion_holds p (K + 1) r LL j M]
  refine forall_congr' fun l => ?_
  show wd p LL j l (X (Fin.last K, c) * h) ∈ SuppLE p LL j M ↔ wd p LL j l h ∈ SuppLE p LL j M
  rw [hw, X_mul_mem]
  simp [wt_single_add, Fin.val_last, hK]

section Last

variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

theorem last_X (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (a b c : Fin r) :
    glAct p LL j a b (X (Fin.last K, c)) = if b = c then X (Fin.last K, a) else 0 := by
  have hK : K < j := by omega
  rw [glAct_X]
  simp [Fin.val_last, hK, hv]

theorem last_wt (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL j 0 (Finsupp.single (Fin.last K, c) 1 + m) = wt LL j 0 m + (if c = 0 then 1 else 0) := by
  have hK : K < j := by omega
  rw [wt_single_add]
  simp [Fin.val_last, hK, hv]

theorem mulLast_bwd (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hh : h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ))) :
    X (Fin.last K, c) * h ∈ YCond p LL j M := by
  classical
  have hsupp : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤ SuppLE p LL j M := by
    rw [Submodule.span_le]
    rintro _ ⟨d, g, hg, rfl⟩
    have hg' := ycond_le_supp (p := p) LL j _ hg
    show X (Fin.last K, d) * g ∈ restrictSupport ℚ_[p] _
    rw [X_mul_mem]
    rw [mem_restrictSupport_iff] at hg' ⊢
    refine hg'.trans ?_
    intro m hm
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [last_wt LL j hj hv]
    rw [← withTop_shift] at hm
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    split_ifs <;> omega
  have hstab : GlStable p LL j (Submodule.span ℚ_[p] {F | ∃ (d : Fin r)
      (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g}) := by
    intro a b x hx
    have key : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
        g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤
        (Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
          g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g}).comap
          (glAct p LL j a b) := by
      rw [Submodule.span_le]
      rintro _ ⟨d, g, hg, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, glAct_mul, last_X p LL j hj hv]
      refine Submodule.add_mem _ ?_
        (Submodule.subset_span ⟨d, _, ycond_glStable (p := p) LL j _ a b g hg, rfl⟩)
      split_ifs
      · exact Submodule.subset_span ⟨a, g, hg, rfl⟩
      · rw [zero_mul]; exact Submodule.zero_mem _
    exact key hx
  have hle : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤ YCond p LL j M := by
    unfold YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (Submodule.subset_span ⟨c, h, hh, rfl⟩)

theorem mulLast_zero (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hg : X (Fin.last K, (0 : Fin r)) * g ∈ YCond p LL j M) :
    g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
  have hcrit := raising_criterion_holds p (K + 1) r LL j M
  have hcrit' := raising_criterion_holds p (K + 1) r LL j (M + ((-1 : ℤ) : WithTop ℤ))
  have hcomm : ∀ d : Fin r, ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 d (X (Fin.last K, (0 : Fin r)) * x) =
        X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x +
          (if d = 0 then X (Fin.last K, (0 : Fin r)) * x else 0) := by
    intro d x
    rw [glAct_mul, last_X p LL j hj hv]
    split_ifs
    · ring
    · simp
  have hP : ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ l : List (Fin r), wd p LL j l (X (Fin.last K, (0 : Fin r)) * x) ∈ SuppLE p LL j M) →
      ∀ d : Fin r, ∀ l : List (Fin r),
        wd p LL j l (X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x) ∈ SuppLE p LL j M := by
    intro x hx d l
    have e : X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x =
        glAct p LL j 0 d (X (Fin.last K, (0 : Fin r)) * x) -
          (if d = 0 then X (Fin.last K, (0 : Fin r)) * x else 0) := by
      rw [hcomm]; abel
    rw [e, map_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [← wd_snoc]; exact hx _
    · split_ifs
      · exact hx l
      · rw [map_zero]; exact Submodule.zero_mem _
  have hC : ∀ l : List (Fin r), ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ l', wd p LL j l' (X (Fin.last K, (0 : Fin r)) * x) ∈ SuppLE p LL j M) →
      ∀ l', wd p LL j l' (X (Fin.last K, (0 : Fin r)) * wd p LL j l x) ∈ SuppLE p LL j M := by
    intro l
    induction l with
    | nil => intro x hx; simpa only [wd_nil] using hx
    | cons d l ih => intro x hx; rw [wd_cons]; exact hP _ (ih x hx) d
  have hB : ∀ y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      X (Fin.last K, (0 : Fin r)) * y ∈ SuppLE p LL j M →
        y ∈ SuppLE p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
    intro y hy
    rw [X_mul_mem, mem_restrictSupport_iff] at hy
    rw [mem_restrictSupport_iff]
    refine hy.trans ?_
    intro m hm
    simp only [Set.mem_setOf_eq, last_wt LL j hj hv] at hm ⊢
    rw [← withTop_shift]
    simpa using hm
  have hg0 : ∀ l : List (Fin r), wd p LL j l (X (Fin.last K, (0 : Fin r)) * g) ∈ SuppLE p LL j M :=
    (hcrit _).mp hg
  refine (hcrit' g).mpr fun l => ?_
  have := hC l g hg0 []
  rw [wd_nil] at this
  exact hB _ this

theorem pow_last (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r) (hc : c ≠ 0)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ) :
    ((glAct p LL j 0 c) ^ (k + 1)) (X (Fin.last K, c) * h) =
      X (Fin.last K, c) * ((glAct p LL j 0 c) ^ (k + 1)) h +
        ((k + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, (0 : Fin r)) * ((glAct p LL j 0 c) ^ k) h) := by
  have h1 : ∀ y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 c (X (Fin.last K, c) * y) =
        X (Fin.last K, (0 : Fin r)) * y + X (Fin.last K, c) * glAct p LL j 0 c y := by
    intro y
    rw [glAct_mul, last_X p LL j hj hv, if_pos rfl]
  have h2 : ∀ z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 c (X (Fin.last K, (0 : Fin r)) * z) =
        X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 c z := by
    intro z
    rw [glAct_mul, last_X p LL j hj hv, if_neg hc, zero_mul, zero_add]
  have hpow : ∀ (n : ℕ) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      ((glAct p LL j 0 c) ^ (n + 1)) y = glAct p LL j 0 c (((glAct p LL j 0 c) ^ n) y) := by
    intro n y
    rw [pow_succ', Module.End.mul_apply]
  induction k with
  | zero =>
    rw [hpow 0, pow_zero, Module.End.one_apply, Module.End.one_apply, h1]
    simp only [zero_add, Nat.cast_one, one_smul]
    abel
  | succ k ih =>
    rw [hpow (k + 1), ih, map_add, map_smul, h1, h2, ← hpow k, ← hpow (k + 1)]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

end Last

theorem mul_last_letter_holds : MulLast := by
  intro p hp K r hr LL j M c h hj hv
  constructor
  · intro hX
    by_cases hc : c = 0
    · subst hc; exact mulLast_zero p LL j M hj hv h hX
    · obtain ⟨n, hn⟩ := raise_nil p LL j c hc h
      have hpowY : ∀ (k : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), x ∈ YCond p LL j M →
          ((glAct p LL j 0 c) ^ k) x ∈ YCond p LL j M := by
        intro k
        induction k with
        | zero => intro x hx; simpa using hx
        | succ k ih =>
          intro x hx
          rw [pow_succ', Module.End.mul_apply]
          exact ycond_glStable (p := p) LL j M 0 c _ (ih x hx)
      have key : ∀ t i : ℕ, i + t = n →
          ((glAct p LL j 0 c) ^ i) h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
        intro t
        induction t with
        | zero =>
          intro i hi
          rw [add_zero] at hi
          subst hi
          rw [hn]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro i hi
          have h1 := ih (i + 1) (by omega)
          have h2 := mulLast_bwd p LL j M hj hv c _ h1
          have h3 := hpowY (i + 1) _ hX
          rw [pow_last p LL j hj hv c hc h i] at h3
          have h4 : ((i + 1 : ℕ) : ℚ_[p]) • (X (Fin.last K, (0 : Fin r)) * ((glAct p LL j 0 c) ^ i) h) ∈
              YCond p LL j M := by
            have := Submodule.sub_mem _ h3 h2
            simpa using this
          have hne : ((i + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)
          have h5 := Submodule.smul_mem _ ((i + 1 : ℕ) : ℚ_[p])⁻¹ h4
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
          exact mulLast_zero p LL j M hj hv _ h5
      simpa using key n 0 (by omega)
  · intro hh
    exact mulLast_bwd p LL j M hj hv c h hh

end Formalism.InvariantFactorPaths.L4
