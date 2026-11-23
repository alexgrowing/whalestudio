import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePE0

section Seq

variable {C : Type} [Field C] {V : VF C}

def Tends (V : VF C) (s : ℕ → C) (x : C) : Prop := ∀ w : ℝ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge w (x - s n)

private theorem ge_zero_lemma (w : ℝ) : V.Ge w (0 : C) := by
  show (w : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

private theorem ge_add_lemma_2 {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) := by
  show (w : WithTop ℝ) ≤ V.v (a + b)
  exact le_trans (le_min ha hb) (AddValuation.map_add V.v a b)

private theorem ge_neg_lemma_3 {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  show (w : WithTop ℝ) ≤ V.v (-a)
  rw [AddValuation.map_neg]
  exact ha

private theorem ge_sub_lemma_4 {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a - b) := by
  rw [sub_eq_add_neg]
  exact ge_add_lemma_2 ha (ge_neg_lemma_3 hb)

private theorem ge_mono_lemma_5 {w w' : ℝ} {a : C} (h : w' ≤ w) (ha : V.Ge w a) : V.Ge w' a := by
  show (w' : WithTop ℝ) ≤ V.v a
  exact le_trans (WithTop.coe_le_coe.mpr h) ha

private theorem ge_mul_lemma_6 {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) :
    V.Ge (w + w') (a * b) := by
  show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb

private theorem ge_tele_lemma_7 {s : ℕ → C} {w : ℝ} {a : ℕ} (h : ∀ m ≥ a, V.Ge w (s (m + 1) - s m)) :
    ∀ b ≥ a, V.Ge w (s b - s a) := by
  intro b (hb : a ≤ b)
  induction b, hb using Nat.le_induction with
  | base =>
    rw [sub_self]
    exact ge_zero_lemma w
  | succ b hab ih =>
    have e : s (b + 1) - s a = (s (b + 1) - s b) + (s b - s a) := by ring
    rw [e]
    exact ge_add_lemma_2 (h b hab) ih

theorem exists_ge (x : C) : ∃ K : ℝ, V.Ge K x := by
  show ∃ K : ℝ, ((K : WithTop ℝ) ≤ V.v x)
  generalize V.v x = t
  induction t using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe r => exact ⟨r, le_rfl⟩

theorem eq_zero_of_ge_all {x : C} (h : ∀ w : ℝ, V.Ge w x) : x = 0 := by
  change ∀ w : ℝ, ((w : WithTop ℝ) ≤ V.v x) at h
  by_contra hx
  have hne : V.v x ≠ ⊤ := by
    intro ht
    apply hx
    first
    | exact (AddValuation.top_iff V.v).mp ht
    | exact V.v.top_iff.mp ht
    | (by_contra hx0
       have h2 : V.v (x * x⁻¹) = V.v x + V.v x⁻¹ := AddValuation.map_mul V.v x x⁻¹
       rw [mul_inv_cancel₀ hx0, AddValuation.map_one, ht, top_add] at h2
       simp at h2)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have h1 := h (r + 1)
  rw [← hr, WithTop.coe_le_coe] at h1
  linarith

theorem tends_const (x : C) : Tends V (fun _ => x) x := by
  intro w
  refine ⟨0, fun n _ => ?_⟩
  show V.Ge w (x - x)
  rw [sub_self]
  exact ge_zero_lemma w

theorem Tends.unique {s : ℕ → C} {x y : C} (hx : Tends V s x) (hy : Tends V s y) : x = y := by
  have hxy : x - y = 0 := by
    apply eq_zero_of_ge_all (V := V)
    intro w
    obtain ⟨n1, h1⟩ := hx w
    obtain ⟨n2, h2⟩ := hy w
    have e : x - y = (x - s (max n1 n2)) - (y - s (max n1 n2)) := by ring
    rw [e]
    exact ge_sub_lemma_4 (h1 _ (le_max_left _ _)) (h2 _ (le_max_right _ _))
  exact sub_eq_zero.mp hxy

theorem Tends.add {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n + t n) (x + y) := by
  intro w
  obtain ⟨n1, h1⟩ := hs w
  obtain ⟨n2, h2⟩ := ht w
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have e : x + y - (s n + t n) = (x - s n) + (y - t n) := by ring
  show V.Ge w (x + y - (s n + t n))
  rw [e]
  exact ge_add_lemma_2 (h1 n (le_of_max_le_left hn)) (h2 n (le_of_max_le_right hn))

theorem Tends.neg {s : ℕ → C} {x : C} (hs : Tends V s x) : Tends V (fun n => -s n) (-x) := by
  intro w
  obtain ⟨n0, h0⟩ := hs w
  refine ⟨n0, fun n hn => ?_⟩
  have e : -x - -s n = -(x - s n) := by ring
  show V.Ge w (-x - -s n)
  rw [e]
  exact ge_neg_lemma_3 (h0 n hn)

theorem Tends.sub {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n - t n) (x - y) := by
  intro w
  obtain ⟨n1, h1⟩ := hs w
  obtain ⟨n2, h2⟩ := ht w
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have e : x - y - (s n - t n) = (x - s n) - (y - t n) := by ring
  show V.Ge w (x - y - (s n - t n))
  rw [e]
  exact ge_sub_lemma_4 (h1 n (le_of_max_le_left hn)) (h2 n (le_of_max_le_right hn))

theorem Tends.mul {s t : ℕ → C} {x y : C} (hs : Tends V s x) (ht : Tends V t y) :
    Tends V (fun n => s n * t n) (x * y) := by
  obtain ⟨Kx, hKx⟩ := exists_ge (V := V) x
  obtain ⟨Ky, hKy⟩ := exists_ge (V := V) y
  intro w
  obtain ⟨n1, h1⟩ := hs (w + |Kx| + |Ky| + |w|)
  obtain ⟨n2, h2⟩ := ht (w + |Kx| + |Ky| + |w|)
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have a1 := h1 n (le_of_max_le_left hn)
  have a2 := h2 n (le_of_max_le_right hn)
  have e : x * y - s n * t n = x * (y - t n) + (x - s n) * y - (x - s n) * (y - t n) := by ring
  show V.Ge w (x * y - s n * t n)
  rw [e]
  have k1 := neg_abs_le Kx
  have k2 := neg_abs_le Ky
  have k3 := neg_abs_le w
  have k4 := abs_nonneg Kx
  have k5 := abs_nonneg Ky
  have k6 := abs_nonneg w
  refine ge_sub_lemma_4 (ge_add_lemma_2 ?_ ?_) ?_
  · exact ge_mono_lemma_5 (by linarith) (ge_mul_lemma_6 hKx a2)
  · exact ge_mono_lemma_5 (by linarith) (ge_mul_lemma_6 a1 hKy)
  · exact ge_mono_lemma_5 (by linarith) (ge_mul_lemma_6 a1 a2)

theorem Tends.sum {ι : Type} (S : Finset ι) {s : ι → ℕ → C} {x : ι → C}
    (h : ∀ i ∈ S, Tends V (s i) (x i)) : Tends V (fun n => ∑ i ∈ S, s i n) (∑ i ∈ S, x i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact tends_const (V := V) 0
  · intro i S hi ih h
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i S)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Tends.ge0 {s : ℕ → C} {x : C} (h : Tends V s x) (hs : ∀ n, V.Ge 0 (s n)) : V.Ge 0 x := by
  obtain ⟨n0, hn⟩ := h 0
  have h1 := ge_add_lemma_2 (hn n0 le_rfl) (hs n0)
  rwa [sub_add_cancel] at h1

theorem exists_tends
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {s : ℕ → C} (hs : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (s (n + 1) - s n)) : ∃ x, Tends V s x := by
  choose φ hφ using hs
  obtain ⟨ψ, hψφ, hψle⟩ : ∃ ψ : ℕ → ℕ, (∀ N, φ N ≤ ψ N) ∧ (∀ N M, N ≤ M → ψ N ≤ ψ M) :=
    ⟨fun N => ∑ k ∈ Finset.range (N + 1), φ k,
      fun N => Finset.single_le_sum (f := φ) (fun k _ => Nat.zero_le (φ k))
        (Finset.mem_range.mpr (Nat.lt_succ_self N)),
      fun N M h => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))⟩
  have tail : ∀ N : ℕ, ∀ n ≥ ψ N, V.Ge (N : ℝ) (s n - s (ψ N)) := fun N =>
    ge_tele_lemma_7 (fun m hm => hφ N m (le_trans (hψφ N) hm))
  obtain ⟨x, hx⟩ := hc (fun N => s (ψ N))
    (fun N => tail N (ψ (N + 1)) (hψle N (N + 1) (Nat.le_succ N)))
  refine ⟨x, ?_⟩
  intro w
  refine ⟨ψ ⌈w⌉₊, fun n hn => ?_⟩
  have A : V.Ge ((⌈w⌉₊ : ℕ) : ℝ) (x - s (ψ ⌈w⌉₊)) := hx ⌈w⌉₊
  have B := tail ⌈w⌉₊ n hn
  have e : x - s n = (x - s (ψ ⌈w⌉₊)) - (s n - s (ψ ⌈w⌉₊)) := by ring
  rw [e]
  exact ge_mono_lemma_5 (Nat.le_ceil w) (ge_sub_lemma_4 A B)

end Seq

section Ser

variable {C : Type} [Field C] {V : VF C} {σ : Type}

def TendsS (V : VF C) (f : ℕ → MvPowerSeries σ C) (g : MvPowerSeries σ C) : Prop :=
  ∀ μ, Tends V (fun n => coeff μ (f n)) (coeff μ g)

theorem TendsS.const (g : MvPowerSeries σ C) : TendsS V (fun _ => g) g := by
  intro μ
  exact tends_const _

theorem TendsS.unique {f : ℕ → MvPowerSeries σ C} {F G : MvPowerSeries σ C} (hF : TendsS V f F)
    (hG : TendsS V f G) : F = G := by
  exact MvPowerSeries.ext fun μ => (hF μ).unique (hG μ)

theorem TendsS.add {f g : ℕ → MvPowerSeries σ C} {F G : MvPowerSeries σ C} (hf : TendsS V f F)
    (hg : TendsS V g G) : TendsS V (fun n => f n + g n) (F + G) := by
  intro μ
  simpa only [map_add] using (hf μ).add (hg μ)

theorem TendsS.sub {f g : ℕ → MvPowerSeries σ C} {F G : MvPowerSeries σ C} (hf : TendsS V f F)
    (hg : TendsS V g G) : TendsS V (fun n => f n - g n) (F - G) := by
  intro μ
  simpa only [map_sub] using (hf μ).sub (hg μ)

theorem TendsS.mul {f g : ℕ → MvPowerSeries σ C} {F G : MvPowerSeries σ C} (hf : TendsS V f F)
    (hg : TendsS V g G) : TendsS V (fun n => f n * g n) (F * G) := by
  classical
  intro μ
  have key := Tends.sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (s := fun p n => coeff p.1 (f n) * coeff p.2 (g n)) (x := fun p => coeff p.1 F * coeff p.2 G)
    (fun p _ => (hf p.1).mul (hg p.2))
  simpa only [MvPowerSeries.coeff_mul] using key

theorem TendsS.pow {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C} (hf : TendsS V f F) (k : ℕ) :
    TendsS V (fun n => f n ^ k) (F ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using TendsS.const (V := V) (1 : MvPowerSeries σ C)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem TendsS.prod {ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} {F : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, TendsS V (f i) (F i)) : TendsS V (fun n => ∏ i ∈ S, f i n) (∏ i ∈ S, F i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa only [Finset.prod_empty] using TendsS.const (V := V) (1 : MvPowerSeries σ C)
  · intro i S hi ih h
    simpa only [Finset.prod_insert hi] using
      (h i (Finset.mem_insert_self i S)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem TendsS.fprod {ι : Type} (d : ι →₀ ℕ) {a : ℕ → ι → MvPowerSeries σ C} {A : ι → MvPowerSeries σ C}
    (ha : ∀ i, TendsS V (fun n => a n i) (A i)) :
    TendsS V (fun n => d.prod fun i e => a n i ^ e) (d.prod fun i e => A i ^ e) := by
  simp only [Finsupp.prod]
  exact TendsS.prod d.support (f := fun i n => a n i ^ d i) (F := fun i => A i ^ d i)
    (fun i _ => (ha i).pow (d i))

theorem TendsS.intS {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C} (hf : TendsS V f F)
    (hi : ∀ n, IntS V (f n)) : IntS V F := by
  intro μ
  exact (hf μ).ge0 (fun n => hi n μ)

def Ord (k : ℕ) (f : MvPowerSeries σ C) : Prop := ∀ μ : σ →₀ ℕ, Finsupp.degree μ < k → coeff μ f = 0

theorem Ord.mul {k k' : ℕ} {f g : MvPowerSeries σ C} (hf : Ord k f) (hg : Ord k' g) : Ord (k + k') (f * g) := by
  classical
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree μ := by
    rw [← hp, map_add]
  by_cases h1 : Finsupp.degree p.1 < k
  · rw [hf p.1 h1, zero_mul]
  · have h2 : Finsupp.degree p.2 < k' := by omega
    rw [hg p.2 h2, mul_zero]

theorem Ord.one : Ord 0 (1 : MvPowerSeries σ C) := by
  intro μ h
  exact absurd h (Nat.not_lt_zero _)

theorem Ord.mono {k k' : ℕ} {f : MvPowerSeries σ C} (hf : Ord k f) (h : k' ≤ k) : Ord k' f := by
  intro μ hμ
  exact hf μ (lt_of_lt_of_le hμ h)

theorem Ord.pow {k : ℕ} {f : MvPowerSeries σ C} (hf : Ord k f) (e : ℕ) : Ord (k * e) (f ^ e) := by
  induction e with
  | zero => simpa only [mul_zero, pow_zero] using (Ord.one : Ord 0 (1 : MvPowerSeries σ C))
  | succ e ih =>
    rw [pow_succ, mul_add, mul_one]
    exact ih.mul hf

theorem ord_one_of_const {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : Ord 1 f := by
  intro μ hμ
  have h0 : μ = 0 := by
    have hd : Finsupp.degree μ = 0 := by omega
    exact (Finsupp.degree_eq_zero_iff μ).mp hd
  subst h0
  first
  | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hf)
  | simpa using hf

theorem Ord.prod {ι : Type} (S : Finset ι) {k : ι → ℕ} {f : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, Ord (k i) (f i)) : Ord (∑ i ∈ S, k i) (∏ i ∈ S, f i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.prod_empty]
    exact Ord.one
  · intro i S hi ih h
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i S)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ord_fprod {τ : Type} {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) (d : σ →₀ ℕ) :
    Ord (Finsupp.degree d) (d.prod fun s e => a s ^ e) := by
  have hdeg : Finsupp.degree d = ∑ s ∈ d.support, d s := by
    first
    | rfl
    | simp [Finsupp.degree_apply]
    | simp [Finsupp.degree]
  rw [hdeg]
  simp only [Finsupp.prod]
  exact Ord.prod d.support (k := fun s => d s) (f := fun s => a s ^ d s)
    (fun s _ => by simpa only [one_mul] using (ord_one_of_const (ha s)).pow (d s))

theorem coeff_subst_eq_sum [Finite σ] {τ : Type} {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (μ : τ →₀ ℕ) :
    coeff μ (subst a f) = ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
      coeff d f * coeff μ (d.prod fun s e => a s ^ e) := by
  have hs : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩
  rw [MvPowerSeries.coeff_subst hs]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  simp only [Function.mem_support, ne_eq] at hd
  by_contra hlt
  exact hd (by rw [ord_fprod ha d μ (by omega), mul_zero])

theorem TendsS.subst [Finite σ] {τ : Type} {a : ℕ → σ → MvPowerSeries τ C} {A : σ → MvPowerSeries τ C}
    {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (hA0 : ∀ s, constantCoeff (A s) = 0)
    (ha : ∀ s, TendsS V (fun n => a n s) (A s)) (hf : TendsS V f F) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst A F) := by
  intro μ
  have key := Tends.sum (V := V) (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset
    (s := fun d n => coeff d (f n) * coeff μ (d.prod fun s e => a n s ^ e))
    (x := fun d => coeff d F * coeff μ (d.prod fun s e => A s ^ e))
    (fun d _ => (hf d).mul (TendsS.fprod d ha μ))
  have hsub := fun n => coeff_subst_eq_sum (ha0 n) (f n) μ
  simp only [hsub, coeff_subst_eq_sum hA0]
  exact key

end Ser

end RowTiePE0

end Formalism.L2.FormalSeriesBounds
