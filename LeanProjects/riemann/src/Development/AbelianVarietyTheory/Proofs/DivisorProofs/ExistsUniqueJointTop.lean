import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.CompactHarm

variable {σ τ : Type} {k l m p q : ℕ}

def JointTop (z : Fin k × Fin m → σ) (y : Fin l × Fin m → σ) (κ : Fin m → ℂ) (α : Fin k → ℂ)
    (β : Fin l → ℂ) (P : MvPolynomial σ ℂ) : Prop :=
  (∀ i j, i < j → mixedOp ℂ z y i j P = 0) ∧ (∀ i, mixedOp ℂ z y i i P = κ i • P) ∧
  (∀ c c', c < c' → rowOp ℂ z c c' P = 0) ∧ (∀ c, rowOp ℂ z c c P = α c • P) ∧
  (∀ d d', d < d' → rowOp ℂ y d d' P = 0) ∧ (∀ d, rowOp ℂ y d d P = β d • P) ∧
  ∀ c d, ∑ i, pderiv (z (c, i)) (pderiv (y (d, i)) P) = 0

theorem row_degree (z : Fin k × Fin m → σ) {P : MvPolynomial σ ℂ} {c : Fin k} {w : ℂ}
    (h : rowOp ℂ z c c P = w • P) {s : σ →₀ ℕ} (hs : s ∈ P.support) :
    ((∑ i, s (z (c, i)) : ℕ) : ℂ) = w := by
  have := congrArg (coeff s) h
  rw [rowOp_apply, coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hs) this
  exact_mod_cast h2

theorem col_degree (z : Fin k × Fin m → σ) (y : Fin l × Fin m → σ) {P : MvPolynomial σ ℂ}
    {i : Fin m} {w : ℂ} (h : mixedOp ℂ z y i i P = w • P) {s : σ →₀ ℕ} (hs : s ∈ P.support) :
    ((∑ c, (s (z (c, i)) : ℤ) - ∑ d, (s (y (d, i)) : ℤ) : ℤ) : ℂ) = w := by
  have := congrArg (coeff s) h
  rw [mixedOp_apply, coeff_sub, coeff_sum, coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, ← sub_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hs) this
  exact_mod_cast h2

theorem notMem_vars_of_row (z : Fin k × Fin m → σ) {P : MvPolynomial σ ℂ} {c : Fin k}
    (h : rowOp ℂ z c c P = (0 : ℂ) • P) (i : Fin m) : z (c, i) ∉ P.vars := by
  classical
  intro hv
  obtain ⟨s, hs, hv⟩ := (mem_vars_iff_mem_support _).1 hv
  have h0 : ∑ i, s (z (c, i)) = 0 := by exact_mod_cast row_degree z h hs
  exact Finsupp.mem_support_iff.1 hv (Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_univ _))

theorem row_invariant [DecidableEq σ] (z : Fin k × Fin m → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ ℂ) {a b : Fin k} (hab : a < b) :
    rowOp ℂ z a b P = 0 ↔ ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ i, if s = z (b, i) then C t * X (z (a, i)) else 0) P = P := by
  rw [rowOp_apply]
  exact (rowAdd_invariant_iff (fun k => z (a, k)) (fun k => z (b, k))
      (fun k l e => by simpa using hz e)
      (fun k l e => hab.ne (congrArg Prod.fst (hz e))) P).out 2 1

theorem polar_homog (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (h : P.IsHomogeneous d) :
    (polar ℂ u v P).IsHomogeneous d := by
  rw [polar_apply]
  rcases d with _ | d
  · have := h.totalDegree_le
    rw [Nat.le_zero, totalDegree_eq_zero_iff_eq_C] at this
    rw [this, pderiv_C, mul_zero]
    exact isHomogeneous_zero _ _ _
  · have := (isHomogeneous_X ℂ u).mul (h.pderiv (i := v))
    rwa [Nat.add_sub_cancel, add_comm] at this

theorem colOp_homog {I J : Type} [Fintype I] (z : I × J → σ) (i j : J) {d : ℕ}
    {P : MvPolynomial σ ℂ} (h : P ∈ homogeneousSubmodule σ ℂ d) :
    colOp ℂ z i j P ∈ homogeneousSubmodule σ ℂ d := by
  rw [colOp, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun _ _ => polar_homog _ _ h

theorem finite_homog [Finite σ] (d : ℕ) : FiniteDimensional ℂ (homogeneousSubmodule σ ℂ d) :=
  Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree σ ℂ d) fun P hP =>
    (mem_restrictTotalDegree _ _ _).2 (IsHomogeneous.totalDegree_le hP)

theorem polar_rename (f : τ → σ) (hf : Function.Injective f) (u v : τ) (Q : MvPolynomial τ ℂ) :
    X (f u) * pderiv (f v) (rename f Q) = rename f (X u * pderiv v Q) := by
  rw [pderiv_rename hf, map_mul, rename_X]

theorem jointTop_rename (f : τ → σ) (hf : Function.Injective f) (z : Fin k × Fin m → τ)
    (y : Fin l × Fin m → τ) (κ : Fin m → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ)
    (Q : MvPolynomial τ ℂ) :
    JointTop (f ∘ z) (f ∘ y) κ α β (rename f Q) ↔ JointTop z y κ α β Q := by
  have hi : Function.Injective (rename f : MvPolynomial τ ℂ → MvPolynomial σ ℂ) :=
    rename_injective f hf
  have h0 : ∀ R : MvPolynomial τ ℂ, rename f R = 0 ↔ R = 0 := fun R => map_eq_zero_iff _ hi
  simp only [JointTop, mixedOp_apply, rowOp_apply, Function.comp_apply, polar_rename f hf]
  simp only [pderiv_rename hf, ← map_sum, ← map_sub, ← map_smul, h0, hi.eq_iff]

theorem sum_castLE (hp : p ≤ k) {M : Type} [AddCommMonoid M] (f : Fin k → M)
    (hf : ∀ c : Fin k, p ≤ c → f c = 0) : ∑ c : Fin p, f (Fin.castLE hp c) = ∑ c, f c :=
  Fintype.sum_of_injective (Fin.castLE hp) (Fin.castLE_injective _) _ _
    (fun c hc => hf c (not_lt.1 fun h => hc ⟨⟨c, h⟩, rfl⟩)) fun _ => rfl

theorem rows_restrict (hp : p ≤ k) (z : Fin k × Fin m → σ) (α : Fin k → ℂ)
    (hα : ∀ c : Fin k, p ≤ c → α c = 0) (P : MvPolynomial σ ℂ)
    (hz : ∀ (c : Fin k) i, p ≤ c → z (c, i) ∉ P.vars) :
    ((∀ c c', c < c' → rowOp ℂ z c c' P = 0) ↔
      ∀ c c', c < c' → rowOp ℂ (fun w => z (Fin.castLE hp w.1, w.2)) c c' P = 0) ∧
    ((∀ c, rowOp ℂ z c c P = α c • P) ↔
      ∀ c, rowOp ℂ (fun w => z (Fin.castLE hp w.1, w.2)) c c P = α (Fin.castLE hp c) • P) := by
  have h0 : ∀ c c' : Fin k, p ≤ c' → rowOp ℂ z c c' P = 0 := fun c c' h => by
    rw [rowOp_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [pderiv_eq_zero_of_notMem_vars (hz _ _ h), mul_zero]
  refine ⟨⟨fun h c c' hc => h (Fin.castLE hp c) (Fin.castLE hp c') hc, fun h c c' hc => ?_⟩,
    ⟨fun h c => h (Fin.castLE hp c), fun h c => ?_⟩⟩
  · by_cases h' : p ≤ c'
    · exact h0 _ _ h'
    · have hc' : (c : ℕ) < c' := hc
      exact h ⟨c, by omega⟩ ⟨c', by omega⟩ hc
  · by_cases h' : p ≤ c
    · rw [h0 _ _ h', hα _ h', zero_smul]
    · exact h ⟨c, by omega⟩

theorem jointTop_restrict (hp : p ≤ k) (hq : q ≤ l) (z : Fin k × Fin m → σ)
    (y : Fin l × Fin m → σ) (κ : Fin m → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ)
    (hα : ∀ c : Fin k, p ≤ c → α c = 0) (hβ : ∀ d : Fin l, q ≤ d → β d = 0)
    (P : MvPolynomial σ ℂ) (hz : ∀ (c : Fin k) i, p ≤ c → z (c, i) ∉ P.vars)
    (hy : ∀ (d : Fin l) i, q ≤ d → y (d, i) ∉ P.vars) :
    JointTop z y κ α β P ↔ JointTop (fun w => z (Fin.castLE hp w.1, w.2))
      (fun w => y (Fin.castLE hq w.1, w.2)) κ (fun c => α (Fin.castLE hp c))
      (fun d => β (Fin.castLE hq d)) P := by
  have hm : ∀ i j, mixedOp ℂ (fun w => z (Fin.castLE hp w.1, w.2))
      (fun w => y (Fin.castLE hq w.1, w.2)) i j P = mixedOp ℂ z y i j P := fun i j => by
    rw [mixedOp_apply, mixedOp_apply]
    congr 1
    · exact sum_castLE hp (fun c => X (z (c, i)) * pderiv (z (c, j)) P) fun c hc => by
        rw [pderiv_eq_zero_of_notMem_vars (hz _ _ hc), mul_zero]
    · exact sum_castLE hq (fun c => X (y (c, j)) * pderiv (y (c, i)) P) fun c hc => by
        rw [pderiv_eq_zero_of_notMem_vars (hy _ _ hc), mul_zero]
  obtain ⟨h1, h2⟩ := rows_restrict hp z α hα P hz
  obtain ⟨h3, h4⟩ := rows_restrict hq y β hβ P hy
  simp only [JointTop, hm, h1, h2, h3, h4]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h c d => h _ _, fun h c d => ?_⟩
  by_cases hc : p ≤ c
  · exact Finset.sum_eq_zero fun i _ => by
      rw [pderiv_swap, pderiv_eq_zero_of_notMem_vars (hz _ _ hc), map_zero]
  by_cases hd : q ≤ d
  · exact Finset.sum_eq_zero fun i _ => by
      rw [pderiv_eq_zero_of_notMem_vars (hy _ _ hd), map_zero]
  exact h ⟨c, by omega⟩ ⟨d, by omega⟩

theorem exists_unique_base (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) (ha : Antitone a)
    (hb : Antitone b) :
    ∃ Q₀ : Poly ℂ Unit p q (Fin m), Q₀ ≠ 0 ∧
      JointTop (fun w => xVar () w.1 w.2) (fun w => yVar () w.1 w.2)
        (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d) Q₀ ∧
      ∀ Q, JointTop (fun w => xVar () w.1 w.2) (fun w => yVar () w.1 w.2)
        (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d) Q →
        ∃ r : ℂ, Q = r • Q₀ := by
  classical
  set z : Fin p × Fin m → Var Unit p q (Fin m) := fun w => xVar () w.1 w.2 with hzd
  set y : Fin q × Fin m → Var Unit p q (Fin m) := fun w => yVar () w.1 w.2 with hyd
  have hz : Function.Injective z := fun u w e => by simpa [z, Prod.ext_iff] using e
  have hy : Function.Injective y := fun u w e => by simpa [y, Prod.ext_iff] using e
  have hzy : ∀ u w, z u ≠ y w := fun u w => by simp [z, y]
  let c : Unit → Fin p → ℕ := fun _ => diffOf a
  let c' : Unit → Fin q → ℕ := fun _ => diffOf b
  have hc : ∀ t, partOf (c t) = a := fun _ => partOf_diffOf ha
  have hc' : ∀ t, partOf (c' t) = b := fun _ => partOf_diffOf hb
  let W : Submodule ℂ (Poly ℂ Unit p q (Fin m)) := rowHighest ℂ c c'
  have hs : ∀ t k l, ∀ w ∈ W, colLie ℂ p q t k l w ∈ W := fun t k l w hw =>
    colLie_mem_of_colAct_mem _ (fun g _ hP => colAct_mem_rowHighest g hP) t k l hw
  obtain ⟨v, hv, hv0, hup, μ, hμ⟩ := exists_highest_vector (colLie ℂ p q) colLie_diag_comm
    (iSup_iInf_eigenspace_colLie ℂ Unit p q (Fin m)) W hs (rowHighest_ne_bot h c c')
  have hant := fun t => highest_weight_antitone _ (colLie_lie t) W (hs t) v hv hv0 _ (hup t) (hμ t)
  obtain ⟨r₀, hr₀⟩ := exists_eq_smul_basePoly h c c' hv μ hant
    (fun t k l hkl => (colLie_apply t k l v).symm.trans (hup t k l hkl))
    fun t k => (colLie_apply t k k v).symm.trans (hμ t k)
  obtain ⟨hh, hrx, hry, hix, hiy⟩ := mem_rowHighest_iff_of_charZero.1 hv
  simp only [rowAddX_eq_bind₁, hc] at hix hrx
  simp only [rowAddY_eq_bind₁, hc'] at hiy hry
  have hh' := fun i j => (laplacian_apply () i j v).symm.trans (hh () i j)
  have hup' : ∀ k l, k < l → mixedOp ℂ z y k l v = 0 := fun k l hkl =>
    (mixedOp_apply _ _ _ _ _).trans ((colLie_apply () k l v).symm.trans (hup () k l hkl))
  have hμ' : ∀ k, mixedOp ℂ z y k k v = (μ () k : ℂ) • v := fun k =>
    (mixedOp_apply _ _ _ _ _).trans ((colLie_apply () k k v).symm.trans (hμ () k))
  have hw := weight_eq_mixedWeight h z hz y hy hzy a b ha hb (hrx ()) (hry ()) (hix ()) (hiy ())
    hh' (μ ()) (hant ()) hup' hμ' hv0
  refine ⟨v, hv0, ⟨hup', hw ▸ hμ', fun i j hij => (row_invariant z hz v hij).2 (hix () i j hij),
    fun i => by simpa using rowOp_self z (hrx () i),
    fun i j hij => (row_invariant y hy v hij).2 (hiy () i j hij),
    fun i => by simpa using rowOp_self y (hry () i), hh'⟩, ?_⟩
  rintro Q ⟨g1, g2, g3, g4, g5, g6, g7⟩
  have hQ : Q ∈ rowHighest ℂ c c' := by
    refine mem_rowHighest_iff_of_charZero.2 ⟨fun t i j => (laplacian_apply t i j Q).trans (g7 i j),
      fun t i s hs => ?_, fun t i s hs => ?_, fun t i j hij s => ?_, fun t i j hij s => ?_⟩
    · rw [hc t]; exact Nat.cast_injective (R := ℂ) (row_degree z (g4 i) hs)
    · rw [hc' t]; exact Nat.cast_injective (R := ℂ) (row_degree y (g6 i) hs)
    · rw [rowAddX_eq_bind₁]; exact (row_invariant z hz Q hij).1 (g3 i j hij) s
    · rw [rowAddY_eq_bind₁]; exact (row_invariant y hy Q hij).1 (g5 i j hij) s
  obtain ⟨r, hr⟩ := exists_eq_smul_basePoly h c c' hQ (fun _ => mixedWeight m a b)
    (fun _ => antitone_mixedWeight m ha hb)
    (fun t k l hkl => (mixedOp_apply z y k l Q).symm.trans (g1 k l hkl))
    fun t k => (mixedOp_apply z y k k Q).symm.trans (g2 k)
  have hr0 : r₀ ≠ 0 := fun e => hv0 (by rw [hr₀, e, zero_smul])
  exact ⟨r / r₀, by rw [hr, hr₀, smul_smul, div_mul_cancel₀ _ hr0]⟩

theorem mixedWeight_restrict (hp : p ≤ k) (hq : q ≤ l) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (ha0 : ∀ c : Fin k, p ≤ c → a c = 0) (hb0 : ∀ d : Fin l, q ≤ d → b d = 0) :
    mixedWeight m (fun c => a (Fin.castLE hp c)) (fun d => b (Fin.castLE hq d)) =
      mixedWeight m a b := by
  funext i
  simp only [mixedWeight_apply]
  congr 1
  · split_ifs with h1 h2 h2
    · rfl
    · omega
    · rw [ha0 _ (by simpa using h1)]; rfl
    · rfl
  · split_ifs with h1 h2 h2
    · rfl
    · omega
    · rw [hb0 _ (by simpa using h1)]; rfl
    · rfl

theorem exists_unique_jointTop (z : Fin k × Fin m → σ) (hz : Function.Injective z)
    (y : Fin l × Fin m → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (hs : ∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) (h : p + q ≤ m) (hp : p ≤ k) (hq : q ≤ l)
    (a : Fin k → ℕ) (b : Fin l → ℕ) (ha : Antitone a) (hb : Antitone b)
    (ha0 : ∀ c : Fin k, p ≤ c → a c = 0) (hb0 : ∀ d : Fin l, q ≤ d → b d = 0) :
    ∃ P₀ : MvPolynomial σ ℂ, P₀ ≠ 0 ∧
      JointTop z y (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d) P₀ ∧
      ∀ P, JointTop z y (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d) P →
        ∃ r : ℂ, P = r • P₀ := by
  classical
  let f : Var Unit p q (Fin m) → σ := fun v =>
    Sum.elim (fun c => z (Fin.castLE hp c, v.2.2)) (fun d => y (Fin.castLE hq d, v.2.2)) v.2.1
  have hf : Function.Injective f := by
    rintro ⟨⟨⟩, c | c, i⟩ ⟨⟨⟩, d | d, j⟩ e
    · simpa using hz e
    · exact absurd e (hzy _ _)
    · exact absurd e.symm (hzy _ _)
    · simpa using hy e
  obtain ⟨Q₀, hQ0, hQ, hu⟩ := exists_unique_base h (fun c => a (Fin.castLE hp c))
    (fun d => b (Fin.castLE hq d)) (fun _ _ h => ha h) (fun _ _ h => hb h)
  rw [mixedWeight_restrict hp hq a b ha0 hb0] at hQ hu
  have key : ∀ Q, JointTop z y (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d)
      (rename f Q) ↔ JointTop (fun w => xVar () w.1 w.2) (fun w => yVar () w.1 w.2)
        (fun i => (mixedWeight m a b i : ℂ)) (fun c => a (Fin.castLE hp c))
        (fun d => b (Fin.castLE hq d)) Q := fun Q => by
    rw [jointTop_restrict hp hq z y _ _ _ (fun c hc => by simp [ha0 c hc])
      (fun c hc => by simp [hb0 c hc]), ← jointTop_rename f hf]
    · rfl
    · intro c i hc hv
      obtain ⟨⟨⟨⟩, d | d, j⟩, -, e⟩ := Finset.mem_image.1 (vars_rename f Q hv)
      · have := congrArg (fun w => (w.1 : ℕ)) (hz e)
        have := d.2
        simp at *; omega
      · exact hzy _ _ e.symm
    · intro c i hc hv
      obtain ⟨⟨⟨⟩, d | d, j⟩, -, e⟩ := Finset.mem_image.1 (vars_rename f Q hv)
      · exact hzy _ _ e
      · have := congrArg (fun w => (w.1 : ℕ)) (hy e)
        have := d.2
        simp at *; omega
  refine ⟨rename f Q₀, fun e => hQ0 (rename_injective f hf (e.trans (map_zero _).symm)),
    (key _).2 hQ, fun P hP => ?_⟩
  obtain ⟨Q, rfl⟩ : ∃ Q, rename f Q = P := by
    refine exists_rename_eq_of_vars_subset_range P f hf fun s hsv => ?_
    rcases hs s with ⟨⟨c, i⟩, rfl⟩ | ⟨⟨c, i⟩, rfl⟩
    · by_cases hc : p ≤ c
      · exact absurd hsv (notMem_vars_of_row z (by simpa [ha0 c hc] using hP.2.2.2.1 c) i)
      · exact ⟨((), .inl ⟨c, by omega⟩, i), rfl⟩
    · by_cases hc : q ≤ c
      · exact absurd hsv (notMem_vars_of_row y (by simpa [hb0 c hc] using hP.2.2.2.2.2.1 c) i)
      · exact ⟨((), .inr ⟨c, by omega⟩, i), rfl⟩
  obtain ⟨r, rfl⟩ := hu Q ((key Q).1 hP)
  exact ⟨r, map_smul _ _ _⟩

theorem rows_le [DecidableEq σ] (z : Fin p × Fin m → σ) (hz : Function.Injective z)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (a : Fin p → ℕ) (ha : ∀ c, 0 < a c)
    (hrz : ∀ i, ∀ s ∈ P.support, ∑ k, s (z (i, k)) = a i)
    (hiz : ∀ i j : Fin p, i < j → ∀ t : ℂ,
      bind₁ (fun s => X s + ∑ k, if s = z (j, k) then C t * X (z (i, k)) else 0) P = P) :
    p ≤ m := by
  obtain ⟨s, hs⟩ := support_nonempty.2 hP
  have h₁ := column_degree_le z hz P a hrz hiz Finset.univ s hs
  simp only [fun i => hrz i s hs, Finset.card_univ, Fintype.card_fin] at h₁
  by_contra hlt
  refine absurd h₁ (not_le.2 (Finset.sum_lt_sum_of_subset (Finset.subset_univ _)
    (i := ⟨m, by omega⟩) (Finset.mem_univ _) (by simp) (ha _) fun _ _ _ => Nat.zero_le _))

theorem rows_add_le (z : Fin p × Fin m → σ) (hz : Function.Injective z)
    (y : Fin q × Fin m → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (a : Fin p → ℕ) (b : Fin q → ℕ) (ha : Antitone a) (hb : Antitone b)
    (ha0 : ∀ c, 0 < a c) (hb0 : ∀ c, 0 < b c) (κ : Fin m → ℤ) (hκ : Antitone κ)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0)
    (hJ : JointTop z y (fun i => κ i) (fun c => a c) (fun d => b d) P) :
    p + q ≤ m ∧ κ = mixedWeight m a b := by
  classical
  obtain ⟨hup, hwt, g3, g4, g5, g6, hharm⟩ := hJ
  have hrz : ∀ i, ∀ s ∈ P.support, ∑ k, s (z (i, k)) = a i := fun i s hs =>
    Nat.cast_injective (R := ℂ) (row_degree z (g4 i) hs)
  have hry : ∀ i, ∀ s ∈ P.support, ∑ k, s (y (i, k)) = b i := fun i s hs =>
    Nat.cast_injective (R := ℂ) (row_degree y (g6 i) hs)
  have hiz := fun i j hij => (row_invariant z hz P hij).1 (g3 i j hij)
  have hiy := fun i j hij => (row_invariant y hy P hij).1 (g5 i j hij)
  have hp := rows_le z hz hP a ha0 hrz hiz
  have hq := rows_le y hy hP b hb0 hry hiy
  set A : Fin m → ℤ := fun i => if h : (i : ℕ) < p then (a ⟨i, h⟩ : ℤ) else 0 with hA
  set B : Fin m → ℤ := fun i => if h : m - 1 - (i : ℕ) < q then (b ⟨m - 1 - i, h⟩ : ℤ) else 0
    with hB
  have hA0 : ∀ i, 0 ≤ A i := fun i => by simp only [hA]; split_ifs <;> positivity
  have hB0 : ∀ i, 0 ≤ B i := fun i => by simp only [hB]; split_ifs <;> positivity
  have hmw : mixedWeight m a b = fun i => A i - B i := rfl
  have c := casimir_mixedOp z hz y hy hzy P
  rw [casimir_on_highest _ (mixedOp_lie z hz y hy hzy) P κ hup hwt,
    casimir_rows z hz a hrz hiz, casimir_rows y hy b hry hiy] at c
  simp only [hharm, mul_zero, Finset.sum_const_zero, smul_zero, sub_zero] at c
  rw [← add_smul, ← Int.cast_add] at c
  have c' := Int.cast_injective (smul_left_injective ℂ hP c)
  have ca := casimir_value_mixedWeight (m := m) (q := 0) hp a Fin.elim0
  have cb := casimir_value_mixedWeight (m := m) (p := 0) (by omega) Fin.elim0 b
  have ea : mixedWeight m a (Fin.elim0 : Fin 0 → ℕ) = A := by
    funext i; simp [mixedWeight_apply, hA]
  have eb : mixedWeight m (Fin.elim0 : Fin 0 → ℕ) b = fun i => -B i := by
    funext i; simp [mixedWeight_apply, hB]
  rw [ea] at ca
  rw [eb] at cb
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero, zero_add] at ca cb
  rw [← ca, ← cb] at c'
  have hid : ∑ i : Fin m, (A i - B i) * (A i - B i + m - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin m, κ i * (κ i + m - 1 - 2 * (i : ℕ)) - 2 * ∑ i, A i * B i := by
    rw [c', Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hAB : 0 ≤ ∑ i, A i * B i := Finset.sum_nonneg fun i _ => mul_nonneg (hA0 i) (hB0 i)
  obtain ⟨s, hm⟩ := support_nonempty.2 hP
  have hw := fun k => weight_of_mem_support z y (hwt k) hm
  have hsa : ∑ k, ∑ i, (s (z (i, k)) : ℤ) = ∑ i, (a i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hrz i s hm
  have hsb : ∑ k, ∑ i, (s (y (i, k)) : ℤ) = ∑ i, (b i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hry i s hm
  have hκe : κ = mixedWeight m a b := by
    refine casimir_value_strict κ _ hκ (antitone_mixedWeight m ha hb) (fun i => ?_) ?_ ?_
    · have h₁ := column_degree_le z hz P a hrz hiz
        (Finset.univ.filter fun k : Fin m => (k : ℕ) < i) s hm
      have h₂ := column_degree_le y hy P b hry hiy
        (Finset.univ.filter fun k : Fin m => ¬ (k : ℕ) < i) s hm
      have c₁ : (Finset.univ.filter fun k : Fin m => (k : ℕ) < i).card = min m i :=
        Fin.card_filter_val_lt
      have c₂ : (Finset.univ.filter fun k : Fin m => ¬ (k : ℕ) < i).card = m - i := by
        have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (fun k : Fin m => (k : ℕ) < i)
        rw [c₁, Finset.card_univ, Fintype.card_fin] at this
        omega
      rw [c₁, Finset.filter_congr (q := fun j : Fin p => (j : ℕ) < i)
        (fun j _ => by have := j.2; omega), Finset.sum_comm] at h₁
      rw [c₂, Finset.sum_comm] at h₂
      rw [← Nat.cast_le (α := ℤ)] at h₁ h₂
      simp only [Nat.cast_sum] at h₁ h₂
      rw [← sum_filter_pad hp] at h₁
      rw [← sum_filter_pad_rev hq] at h₂
      have e₁ := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin m => (k : ℕ) < i)
        fun k => ∑ j, (s (y (j, k)) : ℤ)
      have e₂ := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin m => (k : ℕ) < i)
        fun k => if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0
      rw [sum_dite_rev_lt hq fun i => (b i : ℤ)] at e₂
      simp only [← hw, mixedWeight_apply, Finset.sum_sub_distrib]
      linarith
    · simp only [mixedWeight_apply, Finset.sum_sub_distrib]
      rw [sum_dite_lt hp fun i => (a i : ℤ), sum_dite_rev_lt hq fun i => (b i : ℤ),
        ← hsa, ← hsb, ← Finset.sum_sub_distrib]
      simp only [hw]
    · simp only [hmw]
      linarith
  refine ⟨?_, hκe⟩
  have h0 : ∑ i, A i * B i = 0 := by
    rw [hκe] at hid
    simp only [hmw] at hid
    linarith
  by_contra hlt
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hA0 i) (hB0 i)).1 h0
    ⟨p - 1, by omega⟩ (Finset.mem_univ _)
  simp only [hA, hB] at this
  rw [dif_pos (by omega), dif_pos (by omega)] at this
  exact absurd this (mul_pos (by exact_mod_cast ha0 _) (by exact_mod_cast hb0 _)).ne'

theorem exists_support_length (a : Fin k → ℕ) (ha : Antitone a) :
    ∃ p ≤ k, ∀ c : Fin k, 0 < a c ↔ (c : ℕ) < p := by
  classical
  have hex : ∃ n : ℕ, ∀ c : Fin k, n ≤ c → a c = 0 := ⟨k, fun c hc => by have := c.2; omega⟩
  refine ⟨Nat.find hex, Nat.find_min' _ fun c hc => by have := c.2; omega, fun c => ⟨fun h => ?_,
    fun h => ?_⟩⟩
  · by_contra hc
    have := Nat.find_spec hex c (by omega)
    omega
  · have := Nat.find_min hex h
    push Not at this
    obtain ⟨c', h1, h2⟩ := this
    have : a c' ≤ a c := ha h1
    omega

theorem weights_of_jointTop (z : Fin k × Fin m → σ) (hz : Function.Injective z)
    (y : Fin l × Fin m → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
    (hs : ∀ s, (∃ u, z u = s) ∨ ∃ w, y w = s) (κ : Fin m → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (hJ : JointTop z y κ α β P) :
    ∃ (a : Fin k → ℕ) (b : Fin l → ℕ) (p q : ℕ), p + q ≤ m ∧ p ≤ k ∧ q ≤ l ∧
      (∀ c, 0 < a c ↔ (c : ℕ) < p) ∧ (∀ d, 0 < b d ↔ (d : ℕ) < q) ∧
      (κ = fun i => (mixedWeight m a b i : ℂ)) ∧ (α = fun c => (a c : ℂ)) ∧
      (β = fun d => (b d : ℂ)) ∧ P.IsHomogeneous (∑ c, a c + ∑ d, b d) := by
  classical
  obtain ⟨s, hm⟩ := support_nonempty.2 hP
  obtain ⟨a, rfl⟩ : ∃ a : Fin k → ℕ, α = fun c => (a c : ℂ) :=
    ⟨_, funext fun c => (row_degree z (hJ.2.2.2.1 c) hm).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : Fin l → ℕ, β = fun c => (b c : ℂ) :=
    ⟨_, funext fun c => (row_degree y (hJ.2.2.2.2.2.1 c) hm).symm⟩
  obtain ⟨κ', rfl⟩ : ∃ κ' : Fin m → ℤ, κ = fun c => (κ' c : ℂ) :=
    ⟨_, funext fun c => (col_degree z y (hJ.2.1 c) hm).symm⟩
  have hbij : Function.Bijective (Sum.elim z y) := by
    refine ⟨hz.sumElim hy hzy, fun s => ?_⟩
    rcases hs s with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact ⟨.inl u, rfl⟩
    · exact ⟨.inr u, rfl⟩
  have : Finite σ := Finite.of_surjective _ hbij.2
  have := Fintype.ofFinite σ
  have hhom : P.IsHomogeneous (∑ c, a c + ∑ d, b d) := by
    intro t ht
    have ht' := mem_support_iff.2 ht
    change Finsupp.weight (fun _ => 1) t = _
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, ← hbij.sum_comp,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    · exact Finset.sum_congr rfl fun i _ =>
        Nat.cast_injective (R := ℂ) (row_degree z (hJ.2.2.2.1 i) ht')
    · exact Finset.sum_congr rfl fun i _ =>
        Nat.cast_injective (R := ℂ) (row_degree y (hJ.2.2.2.2.2.1 i) ht')
  have := finite_homog (σ := σ) (∑ c, a c + ∑ d, b d)
  have ha : Antitone a := fun i j hij => by
    have := highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (homogeneousSubmodule σ ℂ _)
      (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) P hhom hP
      (fun c => a c) hJ.2.2.1 (fun c => by simpa using hJ.2.2.2.1 c) hij
    exact Int.ofNat_le.1 this
  have hb : Antitone b := fun i j hij => by
    have := highest_weight_antitone (rowOp ℂ y) (rowOp_lie y hy) (homogeneousSubmodule σ ℂ _)
      (fun i j w hw => by rw [rowOp_eq_colOp]; exact colOp_homog _ _ _ hw) P hhom hP
      (fun c => b c) hJ.2.2.2.2.1 (fun c => by simpa using hJ.2.2.2.2.2.1 c) hij
    exact Int.ofNat_le.1 this
  have hκ : Antitone κ' :=
    highest_weight_antitone (mixedOp ℂ z y) (mixedOp_lie z hz y hy hzy)
      (homogeneousSubmodule σ ℂ _)
      (fun i j w hw => sub_mem (colOp_homog _ _ _ hw) (colOp_homog _ _ _ hw)) P hhom hP
      κ' hJ.1 hJ.2.1
  obtain ⟨p, hp, hpa⟩ := exists_support_length a ha
  obtain ⟨q, hq, hqb⟩ := exists_support_length b hb
  have ha0 : ∀ c : Fin k, p ≤ c → a c = 0 := fun c hc => by have := hpa c; omega
  have hb0 : ∀ c : Fin l, q ≤ c → b c = 0 := fun c hc => by have := hqb c; omega
  have hJ' := (jointTop_restrict hp hq z y _ _ _ (fun c hc => by simp [ha0 c hc])
    (fun c hc => by simp [hb0 c hc]) P
    (fun c i hc => notMem_vars_of_row z (by simpa [ha0 c hc] using hJ.2.2.2.1 c) i)
    (fun c i hc => notMem_vars_of_row y (by simpa [hb0 c hc] using hJ.2.2.2.2.2.1 c) i)).1 hJ
  obtain ⟨h1, h2⟩ := rows_add_le _ (hz.comp ((Fin.castLE_injective hp).prodMap
    Function.injective_id)) _ (hy.comp ((Fin.castLE_injective hq).prodMap
    Function.injective_id)) (fun _ _ => hzy _ _) (fun c => a (Fin.castLE hp c))
    (fun d => b (Fin.castLE hq d)) (fun _ _ h => ha h) (fun _ _ h => hb h)
    (fun c => (hpa _).2 c.2) (fun c => (hqb _).2 c.2) κ' hκ hP hJ'
  rw [mixedWeight_restrict hp hq a b ha0 hb0] at h2
  exact ⟨a, b, p, q, h1, hp, hq, hpa, hqb, by rw [h2], rfl, rfl, hhom⟩

end GlobalTheory.CompactHarm
