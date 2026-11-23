import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.AlmostFinite

universe w

variable {R : Type} [CommRing R]

def BS (c : R) (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  ∃ k : ℕ, (∀ (x : M) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧
    ∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0

theorem BS.of_pow {c : R} {M : Type w} [AddCommGroup M] [Module R M] (k : ℕ)
    (h : ∀ x : M, c ^ k • x = 0) : BS c M :=
  ⟨k, fun x _ _ => h x, fun x _ => h x⟩

theorem BS.ext {c : R} {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (h₁ : BS c N) (h₂ : BS c (M ⧸ N)) : BS c M := by
  obtain ⟨k₁, t₁, s₁⟩ := h₁
  obtain ⟨k₂, t₂, s₂⟩ := h₂
  have key : ∀ (y : M) (n : ℕ), c ^ n • y ∈ N → c ^ k₂ • y ∈ N := by
    intro y n hy
    have h0 : c ^ n • (N.mkQ y) = 0 := by
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero N).2 hy
    have h1 := t₂ _ _ h0
    rw [← map_smul] at h1
    exact (Submodule.Quotient.mk_eq_zero N).1 h1
  refine ⟨k₁ + k₂, ?_, ?_⟩
  · intro x n hx
    have hm : c ^ k₂ • x ∈ N := key x n (by rw [hx]; exact N.zero_mem)
    have h0 : c ^ n • (⟨_, hm⟩ : N) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [smul_comm, hx, smul_zero]
    have h1 := congrArg Subtype.val (t₁ _ _ h0)
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]
  · intro x hx
    have hx2 : c ^ k₂ • x ∈ N := by
      have h0 : c ^ k₂ • N.mkQ x = 0 := s₂ _ (fun m => by
        obtain ⟨y, hy⟩ := hx m
        exact ⟨N.mkQ y, by rw [hy, map_smul]⟩)
      rw [← map_smul] at h0
      exact (Submodule.Quotient.mk_eq_zero N).1 h0
    have hw : ∀ n : ℕ, ∃ w : N, x = c ^ n • (w : M) := by
      intro n
      obtain ⟨y, hy⟩ := hx (n + k₂)
      have hy2 : c ^ k₂ • y ∈ N := by
        refine key y (k₂ + (n + k₂)) ?_
        rw [pow_add, mul_smul, ← hy]
        exact hx2
      exact ⟨⟨_, hy2⟩, by rw [hy, pow_add, mul_smul]⟩
    obtain ⟨w₀, hw₀⟩ := hw 0
    have hxN : x ∈ N := by
      rw [hw₀]; simp
    have h1 := congrArg Subtype.val (s₁ ⟨x, hxN⟩ (fun n => by
      obtain ⟨w, hw'⟩ := hw n
      exact ⟨w, Subtype.ext (by simpa using hw')⟩))
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [add_comm, pow_add, mul_smul, h1, smul_zero]

theorem BS.of_submodule {c : R} {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (a : ℕ) (hN : ∀ x : M, c ^ a • x ∈ N) (h : BS c N) : BS c M := by
  obtain ⟨k, t, s⟩ := h
  refine ⟨k + a, ?_, ?_⟩
  · intro x n hx
    have h0 : c ^ n • (⟨_, hN x⟩ : N) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [smul_comm, hx, smul_zero]
    have h1 := congrArg Subtype.val (t _ _ h0)
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]
  · intro x hx
    have h1 := congrArg Subtype.val (s ⟨_, hN x⟩ (fun n => by
      obtain ⟨y, hy⟩ := hx n
      refine ⟨⟨_, hN y⟩, Subtype.ext ?_⟩
      simp only [Submodule.coe_smul]
      rw [hy, smul_comm]))
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]

section Base

variable {I : Ideal R} {c : R}

theorem BS.cyclic (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I)
    {M : Type w} [AddCommGroup M] [Module R M] (hM : ∀ i ∈ I, ∀ x : M, i • x = 0)
    (m : M) (hm : ∀ x : M, ∃ r : R, x = r • m) : BS c M := by
  by_cases hJ : ∀ t : R, t • m = 0 → t ∈ I
  · refine ⟨0, ?_, ?_⟩
    · intro x n hx
      obtain ⟨r, rfl⟩ := hm x
      rw [smul_smul] at hx
      rcases hI.mem_or_mem (hJ _ hx) with h | h
      · exact absurd (hI.mem_of_pow_mem _ h) hc
      · simp [hM r h m]
    · intro x hx
      obtain ⟨r, rfl⟩ := hm x
      have hr : r ∈ I := by
        refine hs r (fun n => ?_)
        obtain ⟨y, hy⟩ := hx n
        obtain ⟨s, rfl⟩ := hm y
        rw [smul_smul] at hy
        have h0 : (r - c ^ n * s) ∈ I := hJ _ (by rw [sub_smul, hy, sub_self])
        have h1 : r = c ^ n * s + (r - c ^ n * s) := by ring
        rw [h1]
        exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.2 ⟨s, mul_comm _ _⟩) h0
      simp [hM r hr m]
  · push Not at hJ
    obtain ⟨t, ht, htI⟩ := hJ
    obtain ⟨n, hn⟩ := hv t htI
    obtain ⟨a, ha, i, hi, hai⟩ := Submodule.mem_sup.1 hn
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine BS.of_pow n (fun x => ?_)
    obtain ⟨r, rfl⟩ := hm x
    rw [smul_comm, ← hai, add_smul, mul_smul, ht, smul_zero, hM i hi m, add_zero, smul_zero]

theorem BS.of_gens (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) (a : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M], (∀ i ∈ I, ∀ x : M, i • x = 0) →
      ∀ g : Fin a → M, Submodule.span R (Set.range g) = ⊤ → BS c M := by
  induction a with
  | zero =>
    intro M _ _ _ g hg
    refine BS.of_pow 0 (fun x => ?_)
    have hx : x ∈ Submodule.span R (Set.range g) := by rw [hg]; trivial
    have : Set.range g = ∅ := Set.range_eq_empty g
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  | succ a ih =>
    intro M _ _ hM g hg
    refine BS.ext (Submodule.span R {g 0}) ?_ ?_
    · refine BS.cyclic hI hc hv hs (fun i hi x => Subtype.ext (by simpa using hM i hi x))
        ⟨g 0, Submodule.mem_span_singleton_self _⟩ (fun x => ?_)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 x.2
      exact ⟨r, Subtype.ext (by simpa using hr.symm)⟩
    · refine ih _ (fun i hi x => ?_) (fun j => Submodule.mkQ _ (g j.succ)) ?_
      · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
        rw [← map_smul, hM i hi y, map_zero]
      · rw [eq_top_iff, ← Submodule.range_mkQ (Submodule.span R {g 0}), LinearMap.range_eq_map,
          ← hg, Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · have : Submodule.mkQ (Submodule.span R {g 0}) (g 0) = 0 := by
            exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self (g 0))
          rw [this]
          exact Submodule.zero_mem _
        · exact Submodule.subset_span ⟨j, rfl⟩

theorem BS.of_finite (hfg : I.FG) (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) (s : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M], Module.Finite R M →
      (∀ r ∈ I ^ s, ∀ x : M, r • x = 0) → BS c M := by
  induction s with
  | zero =>
    intro M _ _ _ hM
    refine BS.of_pow 0 (fun x => ?_)
    simpa using hM 1 (by simp) x
  | succ s ih =>
    intro M _ _ hfin hM
    have hN : (I • (⊤ : Submodule R M)).FG := Submodule.FG.smul hfg Module.Finite.fg_top
    refine BS.ext (I • (⊤ : Submodule R M)) ?_ ?_
    · refine ih _ (Module.Finite.iff_fg.2 hN) (fun r hr x => Subtype.ext ?_)
      obtain ⟨x, hx⟩ := x
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      induction hx using Submodule.smul_induction_on' with
      | smul i hi y _ =>
        rw [smul_smul]
        exact hM _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hr hi) y
      | add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]
    · obtain ⟨a, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))
      refine BS.of_gens hI hc hv hs a _ (fun i hi x => ?_) g hg
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.smul_mem_smul hi (Submodule.mem_top (x := y)))

end Base

theorem limit_of_cauchy {c : R} (hc : IsPrecomplete (Ideal.span {c}) R)
    {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M) (hfg : N.FG) (a : ℕ)
    (hN : ∀ x : M, c ^ a • x ∈ N) (x : ℕ → M)
    (hx : ∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) :
    ∃ z : M, ∀ n, ∃ y, z - c ^ a • x n = c ^ n • y := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  choose y hy using hx
  have hr : ∀ n, ∃ r : Fin m → R, ∑ i, r i • g i = c ^ a • y n := by
    intro n
    have := hN (y n)
    rw [← hg] at this
    exact (Submodule.mem_span_range_iff_exists_fun R).1 this
  choose r hr using hr
  let S : Fin m → ℕ → R := fun i n => ∑ j ∈ Finset.range n, c ^ j * r j i
  have hmod : ∀ (u v : R) (n : ℕ),
      u ≡ v [SMOD ((Ideal.span {c}) ^ n • ⊤ : Submodule R R)] ↔ ∃ t, u - v = c ^ n * t := by
    intro u v n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht, mul_comm]⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩
  have hlim : ∀ i, ∃ s : R, ∀ n, ∃ t, S i n - s = c ^ n * t := by
    intro i
    obtain ⟨L, hL⟩ := hc.prec' (S i) (fun {p q} hpq => by
      rw [hmod]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
      refine ⟨- ∑ j ∈ Finset.range d, c ^ j * r (p + j) i, ?_⟩
      simp only [S]
      rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
      simp only [pow_add, mul_assoc]
      ring)
    exact ⟨L, fun n => (hmod _ _ _).1 (hL n)⟩
  choose s t ht using hlim
  have hpart : ∀ n, c ^ a • x n = c ^ a • x 0 + ∑ i, S i n • g i := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have h1 : c ^ a • x (n + 1) = c ^ a • x n + c ^ n • (c ^ a • y n) := by
        rw [smul_comm (c ^ n), ← smul_add, ← hy n]
        congr 1
        abel
      rw [h1, ih, ← hr n, add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [S]
      rw [Finset.sum_range_succ, add_smul, mul_smul]
  refine ⟨c ^ a • x 0 + ∑ i, s i • g i, fun n => ⟨∑ i, (- t i n) • g i, ?_⟩⟩
  rw [hpart n, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_smul, smul_smul, show s i - S i n = c ^ n * - t i n by
    rw [mul_neg, ← ht i n]; ring]

theorem afg_separated_complete :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    IsPrecomplete (Ideal.span {c}) R → (∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) →
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], AFG c M → ∃ k : ℕ,
      (∀ (x : M) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧ (∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) ∧
      ∀ x : ℕ → M, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : M, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y := by
  intro R _ I c hfg hnil hprime _ hv hpre hsep M _ _ hM
  obtain ⟨a, N, hN, hx⟩ := hM
  obtain ⟨s, hs⟩ := hnil
  have hBS : BS c M := by
    by_cases hc : c ∈ I
    · refine BS.of_pow s (fun x => ?_)
      have h0 : c ^ s ∈ I ^ s := Ideal.pow_mem_pow hc s
      rw [hs] at h0
      have h1 : c ^ s = 0 := h0
      simp [h1]
    · refine BS.of_submodule N a hx ?_
      refine BS.of_finite hfg hprime hc hv hsep s _ (Module.Finite.iff_fg.2 hN) (fun r hr y => ?_)
      rw [hs] at hr
      have h1 : r = 0 := hr
      simp [h1]
  obtain ⟨k, ht, hd⟩ := hBS
  refine ⟨k + a, ?_, ?_, ?_⟩
  · intro x n h
    rw [add_comm, pow_add, mul_smul, ht x n h, smul_zero]
  · intro x h
    rw [add_comm, pow_add, mul_smul, hd x h, smul_zero]
  · intro x h
    obtain ⟨z, hz⟩ := limit_of_cauchy hpre N hN a hx x h
    refine ⟨c ^ k • z, fun n => ?_⟩
    obtain ⟨y, hy⟩ := hz n
    refine ⟨c ^ k • y, ?_⟩
    rw [pow_add, mul_smul, ← smul_sub, hy, smul_comm]

end GlobalTheory.CompanionTheory.AlmostFinite
