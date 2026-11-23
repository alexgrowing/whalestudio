import Mathlib

open Matrix

namespace GlobalTheory

namespace LatticeIndicator

theorem exists_injective_comp_eq_of_surjective {k V W : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] (f g : V →ₗ[k] W)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : V →ₗ[k] V, Function.Injective e ∧ g ∘ₗ e = f := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have hrk : Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker g) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hf] at h1
    rw [LinearMap.range_eq_top.2 hg] at h2
    omega
  let θ := LinearEquiv.ofFinrankEq _ _ hrk
  obtain ⟨p, hp⟩ := (LinearMap.ker f).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  have hgs : ∀ w, g (s w) = w := fun w => LinearMap.congr_fun hs w
  have key : ∀ v, g (s (f v) + (θ (p v) : V)) = f v := fun v => by
    rw [map_add, hgs, (θ (p v)).2, add_zero]
  refine ⟨s ∘ₗ f + (LinearMap.ker g).subtype ∘ₗ θ.toLinearMap ∘ₗ p, ?_, LinearMap.ext key⟩
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : s (f v) + (θ (p v) : V) = 0 := hv
  have hfv : f v = 0 := by rw [← key v, hv', map_zero]
  rw [hfv, map_zero, zero_add] at hv'
  have h1 : p v = 0 := θ.map_eq_zero_iff.1 (Subtype.ext hv')
  have h2 : p v = ⟨v, hfv⟩ := LinearMap.congr_fun hp ⟨v, hfv⟩
  rw [h2] at h1
  exact congrArg Subtype.val h1

theorem exists_matrix_of_span_eq_top_field {k W n : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Fintype n] [DecidableEq n] (a b : n → W) (ha : Submodule.span k (Set.range a) = ⊤)
    (hb : Submodule.span k (Set.range b) = ⊤) :
    ∃ g : Matrix n n k, g.det ≠ 0 ∧ ∀ j, a j = ∑ i, g i j • b i := by
  obtain ⟨e, he, hge⟩ := exists_injective_comp_eq_of_surjective
    (Fintype.linearCombination k a) (Fintype.linearCombination k b)
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ha])
    (by rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hb])
  refine ⟨LinearMap.toMatrix' e, ?_, fun j => ?_⟩
  · rw [LinearMap.det_toMatrix']
    exact ((LinearMap.isUnit_iff_isUnit_det e).1
      ((LinearMap.isUnit_iff_ker_eq_bot e).2 (LinearMap.ker_eq_bot.2 he))).ne_zero
  · have := LinearMap.congr_fun hge (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul] at this
    rw [← this]
    simp [Fintype.linearCombination_apply, LinearMap.toMatrix'_apply]

theorem exists_gl_of_span_eq_top {O Q n : Type*} [CommRing O] [IsLocalRing O] [AddCommGroup Q]
    [Module O Q] [Fintype n] [DecidableEq n] (a b : n → Q)
    (ha : Submodule.span O (Set.range a) = ⊤) (hb : Submodule.span O (Set.range b) = ⊤) :
    ∃ g : GL n O, ∀ j, a j = ∑ i, (g : Matrix n n O) i j • b i := by
  set I := IsLocalRing.maximalIdeal O with hI
  letI : Field (O ⧸ I) := Ideal.Quotient.field I
  let π := (I • (⊤ : Submodule O Q)).mkQ
  have hspan : ∀ c : n → Q, Submodule.span O (Set.range c) = ⊤ →
      Submodule.span (O ⧸ I) (Set.range fun i => π (c i)) = ⊤ := by
    intro c hc
    rw [eq_top_iff]
    rintro w -
    have : w ∈ Submodule.span O (Set.range fun i => π (c i)) := by
      have : (Set.range fun i => π (c i)) = π '' Set.range c := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hc, Submodule.map_top, Submodule.range_mkQ]
      trivial
    exact Submodule.span_subset_span O (O ⧸ I) _ this
  obtain ⟨g, hg, hab⟩ := exists_matrix_of_span_eq_top_field _ _ (hspan a ha) (hspan b hb)
  choose g₀ hg₀ using fun i j => Ideal.Quotient.mk_surjective (I := I) (g i j)
  have hdiff : ∀ j, ∃ w : n → O, (∀ i, w i ∈ I) ∧ ∑ i, w i • b i = a j - ∑ i, g₀ i j • b i := by
    intro j
    have h1 : a j - ∑ i, g₀ i j • b i ∈ I • (⊤ : Submodule O Q) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change π _ = 0
      rw [map_sub, hab j, map_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hg₀ i j]
      rfl
    rw [← hb, Submodule.mem_ideal_smul_span_iff_exists_sum] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    refine ⟨w, hw, ?_⟩
    rw [← hw', Finsupp.sum_fintype _ _ (by simp)]
  choose w hwI hw using hdiff
  let G : Matrix n n O := Matrix.of fun i j => g₀ i j + w j i
  have hG : (Ideal.Quotient.mk I).mapMatrix G = g := by
    ext i j
    simp [G, hg₀, Ideal.Quotient.eq_zero_iff_mem.2 (hwI j i)]
  have hdet : IsUnit G.det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hI, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_det, hG]
    exact hg
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det G).2 hdet
  refine ⟨u, fun j => ?_⟩
  rw [hu]
  simp only [G, Matrix.of_apply, add_smul, Finset.sum_add_distrib, hw]
  abel

theorem exists_gl_of_span_eq {O Q n : Type*} [CommRing O] [IsLocalRing O] [AddCommGroup Q]
    [Module O Q] [Fintype n] [DecidableEq n] (a b : n → Q)
    (hab : Submodule.span O (Set.range a) = Submodule.span O (Set.range b)) :
    ∃ g : GL n O, ∀ j, a j = ∑ i, (g : Matrix n n O) i j • b i := by
  set S := Submodule.span O (Set.range b) with hS
  have hspan : ∀ (c : n → Q) (hc : Submodule.span O (Set.range c) = S),
      Submodule.span O (Set.range fun i =>
        (⟨c i, hc ▸ Submodule.subset_span ⟨i, rfl⟩⟩ : S)) = ⊤ := by
    intro c hc
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    exact hc
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq_top _ _ (hspan a hab) (hspan b rfl)
  exact ⟨g, fun j => by simpa using congrArg Subtype.val (hg j)⟩

theorem exists_gl_comp_eq_of_surjective {O Q n : Type*} [CommRing O] [IsLocalRing O]
    [AddCommGroup Q] [Module O Q] [Fintype n] [DecidableEq n] (a b : (n → O) →ₗ[O] Q)
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    ∃ g : GL n O, a = b ∘ₗ Matrix.toLin' (g : Matrix n n O) := by
  have hspan : ∀ c : (n → O) →ₗ[O] Q, Function.Surjective c →
      Submodule.span O (Set.range fun i => c (Pi.basisFun O n i)) = ⊤ := by
    intro c hc
    have : (Set.range fun i => c (Pi.basisFun O n i)) = c '' Set.range (Pi.basisFun O n) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, (Pi.basisFun O n).span_eq, Submodule.map_top,
      LinearMap.range_eq_top.2 hc]
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq_top _ _ (hspan a ha) (hspan b hb)
  refine ⟨g, (Pi.basisFun O n).ext fun j => ?_⟩
  rw [hg j, LinearMap.comp_apply]
  simp_rw [← map_smul, ← map_sum]
  congr 1
  ext i
  simp [Pi.single_apply, Finset.sum_apply]

open Classical in

theorem exists_eq_sum_ite_le {P R : Type*} [PartialOrder P] [Fintype P] [CommRing R]
    (f : P → R) : ∃ c : P → R, ∀ p, f p = ∑ q, c q * (if p ≤ q then 1 else 0) := by
  let v : P → P → R := fun q p => if p ≤ q then 1 else 0
  have hsingle : ∀ q : P, (Pi.single q 1 : P → R) ∈ Submodule.span R (Set.range v) := by
    intro q
    induction q using WellFoundedLT.induction with
    | ind q ih =>
      have : (Pi.single q 1 : P → R) =
          v q - ∑ r ∈ Finset.univ.filter (· < q), (Pi.single r 1 : P → R) := by
        ext p
        simp only [v, Pi.sub_apply, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq,
          Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : p = q
        · simp [h]
        · simp [h, lt_iff_le_and_ne]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨q, rfl⟩)
        (Submodule.sum_mem _ fun r hr => ih r (Finset.mem_filter.1 hr).2)
  have hf : f ∈ Submodule.span R (Set.range v) := by
    rw [pi_eq_sum_univ' f]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hsingle q)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hf
  exact ⟨c, fun p => by rw [← hc]; simp [v, Finset.sum_apply]⟩

theorem exists_matrix_of_smul_mem {O m : Type*} [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [Fintype m] [DecidableEq m] {c : O} (hc : c ≠ 0)
    (L : Submodule O (m → O)) (hL : ∀ v, c • v ∈ L) :
    ∃ h : Matrix m m O, h.det ≠ 0 ∧ ∀ v, v ∈ L ↔ ∃ u, v = h *ᵥ u := by
  have hrk : Module.finrank O L = Fintype.card m := by
    apply le_antisymm
    · simpa using L.finrank_le
    · have := LinearMap.finrank_le_finrank_of_injective
        (f := LinearMap.codRestrict L (c • LinearMap.id) hL) (fun v v' h =>
          smul_right_injective _ hc (congrArg Subtype.val h))
      simpa using this
  let b : Module.Basis m O L :=
    (Module.finBasisOfFinrankEq O L hrk).reindex (Fintype.equivFin m).symm
  let h : Matrix m m O := Matrix.of fun i j => (b j : m → O) i
  have hmul : ∀ u : m → O, h *ᵥ u = ((∑ j, u j • b j : L) : m → O) := by
    intro u
    ext i
    simp [h, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hiff : ∀ v, v ∈ L ↔ ∃ u, v = h *ᵥ u := by
    intro v
    refine ⟨fun hv => ⟨b.repr ⟨v, hv⟩, ?_⟩, ?_⟩
    · rw [hmul, b.sum_repr]
    · rintro ⟨u, rfl⟩
      rw [hmul]
      exact Subtype.property _
  refine ⟨h, ?_, hiff⟩
  choose u hu using fun j : m => (hiff _).1 (hL (Pi.single j 1))
  have : h * Matrix.of (fun i j => u j i) = c • (1 : Matrix m m O) := by
    ext i j
    have := congrFun (hu j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply]
      using this.symm
  have hd := congrArg Matrix.det this
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hd
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ hc hd.symm

theorem finite_quotient_smul_top {O m : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Finite m] {c : O}
    (hc : c ≠ 0) : Finite ((m → O) ⧸ (Ideal.span {c} • (⊤ : Submodule O (m → O)))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hϖ
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ Ideal.span {c}) := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k
  exact Submodule.finite_quotient_smul (Ideal.span {c}) (N := ⊤) Module.Finite.fg_top

theorem eq_of_span_col_eq {O m n R : Type*} [CommRing O] [IsLocalRing O] [Fintype n]
    [DecidableEq n] (c : O) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) (z z' : Matrix m n O)
    (h : Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z.col j)) =
      Submodule.span O
        (Set.range fun j => (Ideal.span {c} • (⊤ : Submodule O (m → O))).mkQ (z'.col j))) :
    ψ z = ψ z' := by
  obtain ⟨g, hg⟩ := exists_gl_of_span_eq _ _ h
  have : ∀ j, ∃ y : m → O, c • y = z.col j - (z' * (g : Matrix n n O)).col j := by
    intro j
    have h1 : z.col j - (z' * (g : Matrix n n O)).col j ∈
        Ideal.span {c} • (⊤ : Submodule O (m → O)) := by
      rw [← Submodule.Quotient.eq]
      have h2 : (z' * (g : Matrix n n O)).col j = ∑ i, (g : Matrix n n O) i j • z'.col i := by
        ext i
        simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
      have h3 := hg j
      simp_rw [← map_smul, ← map_sum] at h3
      rw [h2]
      exact h3
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, -, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using this
  have hz : z = z' * (g : Matrix n n O) + c • Matrix.of fun i j => y j i := by
    ext i j
    have := congrFun (hy j) i
    simp only [Pi.smul_apply, Pi.sub_apply, Matrix.col_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, this]
    ring
  rw [hz, hper, hinv]

open Classical in

theorem exists_eq_sum_ite_integral {O m n R : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [CommRing R] {c : O} (hc : c ≠ 0) (ψ : Matrix m n O → R)
    (hinv : ∀ (z : Matrix m n O) (k : GL n O), ψ (z * (k : Matrix n n O)) = ψ z)
    (hper : ∀ z y : Matrix m n O, ψ (z + c • y) = ψ z) :
    ∃ (r : ℕ) (h : Fin r → Matrix m m O) (a : Fin r → R), (∀ l, (h l).det ≠ 0) ∧
      ∀ z, ψ z = ∑ l, a l * (if ∃ y : Matrix m n O, z = h l * y then 1 else 0) := by
  set A : Submodule O (m → O) := Ideal.span {c} • ⊤ with hA
  haveI : Finite ((m → O) ⧸ A) := finite_quotient_smul_top hc
  haveI : Finite (Submodule O ((m → O) ⧸ A)) :=
    Finite.of_injective _ (SetLike.coe_injective (A := Submodule O ((m → O) ⧸ A)))
  letI := Fintype.ofFinite (Submodule O ((m → O) ⧸ A))
  let Λ : Matrix m n O → Submodule O ((m → O) ⧸ A) := fun z =>
    Submodule.span O (Set.range fun j => A.mkQ (z.col j))
  have hfac : Function.FactorsThrough ψ Λ := fun z z' h => eq_of_span_col_eq c ψ hinv hper z z' h
  obtain ⟨a, ha⟩ := exists_eq_sum_ite_le (Function.extend Λ ψ 0)
  have hL : ∀ (q : Submodule O ((m → O) ⧸ A)) (v : m → O), c • v ∈ q.comap A.mkQ := by
    intro q v
    have : A.mkQ (c • v) = 0 := (Submodule.Quotient.mk_eq_zero A).2
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) trivial)
    rw [Submodule.mem_comap, this]
    exact q.zero_mem
  choose h hdet hh using fun q => exists_matrix_of_smul_mem hc _ (hL q)
  have hiff : ∀ q z, Λ z ≤ q ↔ ∃ y : Matrix m n O, z = h q * y := by
    intro q z
    rw [Submodule.span_le, Set.range_subset_iff]
    constructor
    · intro hz
      choose u hu using fun j => (hh q _).1 (hz j)
      refine ⟨Matrix.of fun i j => u j i, ?_⟩
      ext i j
      exact congrFun (hu j) i
    · rintro ⟨y, rfl⟩ j
      exact (hh q _).2 ⟨y.col j, rfl⟩
  let e := (Fintype.equivFin (Submodule O ((m → O) ⧸ A))).symm
  refine ⟨_, fun l => h (e l), fun l => a (e l), fun l => hdet _, fun z => ?_⟩
  rw [← hfac.extend_apply 0 z, ha, ← e.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hiff]

theorem forall_mem_range_iff {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    (x : Matrix m n K) :
    (∀ i j, x i j ∈ (algebraMap O K).range) ↔
      ∃ y : Matrix m n O, y.map (algebraMap O K) = x := by
  constructor
  · intro h
    choose y hy using h
    exact ⟨Matrix.of y, Matrix.ext hy⟩
  · rintro ⟨y, rfl⟩ i j
    exact ⟨y i j, rfl⟩

theorem forall_mul_map_mem_range_iff {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype n] [DecidableEq n] (x : Matrix m n K) (k : GL n O) :
    (∀ i j, (x * (k : Matrix n n O).map (algebraMap O K)) i j ∈ (algebraMap O K).range) ↔
      ∀ i j, x i j ∈ (algebraMap O K).range := by
  rw [forall_mem_range_iff, forall_mem_range_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y * ((k⁻¹ : GL n O) : Matrix n n O), ?_⟩
    rw [Matrix.map_mul, hy, Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  · rintro ⟨y, rfl⟩
    exact ⟨y * (k : Matrix n n O), Matrix.map_mul⟩

end LatticeIndicator

open LatticeIndicator

section Main

variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

theorem exists_eq_sum_indicator_of_right_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL m K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL m K) : Matrix m m K) * x) := by
  classical
  set f := algebraMap O K with hf
  have hinj : Function.Injective f := IsFractionRing.injective O K
  have ha' : f a ≠ 0 := (map_ne_zero_iff f hinj).2 ha
  obtain ⟨r, h, c, hdet, hψ⟩ := exists_eq_sum_ite_integral (mul_ne_zero ha hb)
    (fun z : Matrix m n O => φ ((f a)⁻¹ • z.map f))
    (fun z k => by rw [Matrix.map_mul, ← Matrix.smul_mul, hinv])
    (fun z y => by
      have : (f a)⁻¹ • (z + (a * b) • y).map f = (f a)⁻¹ • z.map f + f b • y.map f := by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.add_apply, smul_eq_mul, map_add,
          map_mul]
        field_simp
      rw [this, hper _ (y.map f) fun i j => ⟨y i j, rfl⟩])
  have hdet' : ∀ l, ((f a)⁻¹ • (h l).map f).det ≠ 0 := by
    intro l
    rw [Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha')) ?_
    have := RingHom.map_det f (h l)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero_iff f hinj).2 (hdet l)
  let H : Fin r → GL m K := fun l => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet' l)
  have hH : ∀ l, (H l : Matrix m m K) = (f a)⁻¹ • (h l).map f := fun l => rfl
  have hmem : ∀ l (x : Matrix m n K),
      ((((H l)⁻¹ : GL m K) : Matrix m m K) * x ∈
        {y : Matrix m n K | ∀ i j, y i j ∈ f.range}) ↔
      ∃ y : Matrix m n O, f a • x = (h l * y).map f := by
    intro l x
    rw [Set.mem_setOf_eq, hf, forall_mem_range_iff, ← hf]
    refine exists_congr fun y => ?_
    rw [Matrix.map_mul]
    have h1 : (h l).map f = f a • (H l : Matrix m m K) := by
      rw [hH, smul_smul, mul_inv_cancel₀ ha', one_smul]
    rw [h1, Matrix.smul_mul, (smul_right_injective _ ha').eq_iff]
    constructor
    · intro hy
      rw [hy, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · intro hy
      rw [hy, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨r, H, c, fun x => ?_⟩
  by_cases hx : ∃ z : Matrix m n O, z.map f = f a • x
  · obtain ⟨z, hz⟩ := hx
    have h1 := hψ z
    simp only [hz, smul_smul, inv_mul_cancel₀ ha', one_smul] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.indicator_apply]
    have h2 : ∀ y : Matrix m n O, f a • x = (h l * y).map f ↔ z = h l * y := fun y => by
      rw [← hz]
      exact (Matrix.map_injective hinj).eq_iff
    simp only [hmem, h2, Pi.one_apply]
  · have h0 : φ x = 0 := by
      by_contra h0
      exact hx ((forall_mem_range_iff _).1 (hsupp x h0))
    rw [h0]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [Set.indicator_of_notMem, mul_zero]
    rw [hmem]
    rintro ⟨y, hy⟩
    exact hx ⟨_, hy.symm⟩

theorem exists_eq_sum_indicator_of_left_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL m O),
      φ ((k : Matrix m m O).map (algebraMap O K) * x) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (g : Fin r → GL n K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 (x * (g l : Matrix n n K)) := by
  obtain ⟨r, h, c, hφ⟩ := exists_eq_sum_indicator_of_right_invariant ha hb
    (fun x : Matrix n m K => φ xᵀ)
    (fun x k => by
      rw [Matrix.transpose_mul, ← Matrix.transpose_map]
      exact hinv _ ⟨k.valᵀ, k.invᵀ,
        by rw [← Matrix.transpose_mul, k.inv_val, Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, k.val_inv, Matrix.transpose_one]⟩)
    (fun x hx i j => hsupp _ hx j i)
    (fun x y hy => hper xᵀ yᵀ fun i j => hy j i)
  refine ⟨r, fun l => ⟨(h l).invᵀ, (h l).valᵀ,
    by rw [← Matrix.transpose_mul, (h l).val_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, (h l).inv_val, Matrix.transpose_one]⟩, c, fun x => ?_⟩
  refine (hφ xᵀ).trans (Finset.sum_congr rfl fun l _ => ?_)
  congr 1
  have h1 : (((h l)⁻¹ : GL n K) : Matrix n n K) * xᵀ = (x * (h l).invᵀ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]; rfl
  rw [h1]
  by_cases hx : ∀ i j, (x * (h l).invᵀ) i j ∈ (algebraMap O K).range
  · rw [Set.indicator_of_mem (by exact fun i j => hx j i), Set.indicator_of_mem (by exact hx)]
    rfl
  · rw [Set.indicator_of_notMem (by exact fun h' => hx fun i j => h' j i),
      Set.indicator_of_notMem (by exact hx)]

theorem mem_span_indicator_of_right_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    φ ∈ Submodule.span R (Set.range fun (h : GL m K) (x : Matrix m n K) =>
      Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        (1 : Matrix m n K → R) (((h⁻¹ : GL m K) : Matrix m m K) * x)) := by
  obtain ⟨r, h, c, hφ⟩ := exists_eq_sum_indicator_of_right_invariant ha hb φ hinv hsupp hper
  have : φ = ∑ l, c l • fun x : Matrix m n K =>
      Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        (1 : Matrix m n K → R) ((((h l)⁻¹ : GL m K) : Matrix m m K) * x) := by
    ext x
    rw [hφ x, Finset.sum_apply]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h l, rfl⟩)

end Main

theorem invariant_testFun_eq_sum_indicator {O K : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) {M n : ℕ} (N : ℕ)
    (φ : Matrix (Fin M) (Fin n) K → ℂ)
    (hinv : ∀ (x : Matrix (Fin M) (Fin n) K) (k : GL (Fin n) O),
      φ (x * (k : Matrix (Fin n) (Fin n) O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix (Fin M) (Fin n) K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K ϖ ^ N • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix (Fin M) (Fin n) K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K ϖ ^ N • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL (Fin M) K) (c : Fin r → ℂ), ∀ x : Matrix (Fin M) (Fin n) K,
      φ x = ∑ l, c l * Set.indicator
        {y : Matrix (Fin M) (Fin n) K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K) * x) :=
  exists_eq_sum_indicator_of_right_invariant (pow_ne_zero N hϖ.ne_zero) (pow_ne_zero N hϖ.ne_zero)
    φ hinv (by simpa only [map_pow] using hsupp) (by simpa only [map_pow] using hper)

end GlobalTheory
