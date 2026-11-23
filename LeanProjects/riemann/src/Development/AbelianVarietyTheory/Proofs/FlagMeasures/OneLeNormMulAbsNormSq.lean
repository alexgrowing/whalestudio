import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory.DefinitePacking

theorem exists_diag {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x : V, x ≠ 0 → h x x ≠ 0) (s : ℕ) :
    ∀ W : Submodule K V, finrank K W ≤ s → ∃ (f : Fin s → V →ₗ[K] K) (e : Fin s → V),
      ∀ x ∈ W, h x x = ∑ i, star (f i x) * f i x * h (e i) (e i) := by
  induction s with
  | zero =>
    intro W hW
    have : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    subst this
    refine ⟨fun _ => 0, fun _ => 0, fun x hx => ?_⟩
    rw [Submodule.mem_bot] at hx
    simp [hx]
  | succ n ih =>
    intro W hW
    by_cases h0 : W = ⊥
    · subst h0
      refine ⟨fun _ => 0, fun _ => 0, fun x hx => ?_⟩
      rw [Submodule.mem_bot] at hx
      simp [hx]
    obtain ⟨e, heW, he⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hee := ha e he
    have hlt : W ⊓ LinearMap.ker (h e) < W := by
      refine lt_of_le_of_ne inf_le_left fun hc => ?_
      have : e ∈ W ⊓ LinearMap.ker (h e) := by rw [hc]; exact heW
      exact hee this.2
    have hr := Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨f, e', hf⟩ := ih (W ⊓ LinearMap.ker (h e)) (by omega)
    let g : V →ₗ[K] K := (h e e)⁻¹ • h e
    let P : V →ₗ[K] V := LinearMap.id - g.smulRight e
    refine ⟨Fin.cons g (fun i => f i ∘ₗ P), Fin.cons e e', fun x hx => ?_⟩
    have hP : P x = x - g x • e := rfl
    have hg : g x * h e e = h e x := by
      simp only [g, LinearMap.smul_apply, smul_eq_mul]
      field_simp
    have hk : h e (P x) = 0 := by
      rw [hP, map_sub, map_smul, smul_eq_mul, hg, sub_self]
    have hk' : h (P x) e = 0 := by
      rw [← hs.eq e (P x), hk, map_zero]
    have hmem : P x ∈ W ⊓ LinearMap.ker (h e) :=
      ⟨by rw [hP]; exact W.sub_mem hx (W.smul_mem _ heW), hk⟩
    have hx' : x = P x + g x • e := by rw [hP]; abel
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
    rw [← hf _ hmem]
    generalize P x = y at *
    generalize g x = c at *
    rw [hx']
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, hk, hk', starRingEnd_apply]
    ring

theorem one_le_norm_mul_absNorm {K : Type} [Field K] [NumberField K] (c : K) (hc : c ≠ 0)
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (h : ∀ a ∈ J, ∃ o : 𝓞 K, (o : K) = c * a) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ c : ℚ) : ℝ)| * (Ideal.absNorm J : ℝ) := by
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hc
  have hle : Ideal.span {a} * J ≤ Ideal.span {d} := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro z hz
    obtain ⟨o, ho⟩ := h z hz
    rw [Ideal.mem_span_singleton']
    refine ⟨o, ?_⟩
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, map_mul]
    change (o : K) * _ = _ * (z : K)
    rw [ho]
    field_simp
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hne : Ideal.absNorm (Ideal.span {a} * J) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact mul_ne_zero (by simpa using ha0) hJ
  have hl := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at hl
  have hl' : (((Algebra.norm ℤ d).natAbs : ℕ) : ℝ) ≤ (((Algebra.norm ℤ a).natAbs : ℕ) : ℝ) * (Ideal.absNorm J : ℝ) := by
    exact_mod_cast hl
  have key : ∀ z : 𝓞 K, (((Algebra.norm ℤ z).natAbs : ℕ) : ℝ) = |((Algebra.norm ℚ (z : K) : ℚ) : ℝ)| := by
    intro z
    rw [← Algebra.coe_norm_int, Nat.cast_natAbs]
    push_cast
    rfl
  rw [key, key] at hl'
  have hdn : (0 : ℝ) < |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hdK)
  have hm : Algebra.norm ℚ (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K d) * Algebra.norm ℚ (d : K)
      = Algebra.norm ℚ (a : K) := by
    rw [← map_mul]
    congr 1
    exact div_mul_cancel₀ _ hdK
  rw [← hm] at hl'
  push_cast at hl'
  rw [abs_mul] at hl'
  refine le_of_mul_le_mul_right ?_ hdn
  linarith

theorem absNorm_map_equiv {K : Type} [Field K] [NumberField K] (e : 𝓞 K ≃+* 𝓞 K)
    (I : Ideal (𝓞 K)) : Ideal.absNorm (I.map (e : 𝓞 K →+* 𝓞 K)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ e rfl).toEquiv).symm

theorem one_le_norm_mul_absNorm_sq {K : Type} [Field K] [NumberField K] [StarRing K] (c : K)
    (hc : c ≠ 0) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (h : ∀ a ∈ I, ∀ b ∈ I, ∃ o : 𝓞 K, (o : K) = c * (star (a : K) * b)) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ c : ℚ) : ℝ)| * (Ideal.absNorm I : ℝ) ^ 2 := by
  let e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)
  have he : ∀ a : 𝓞 K, (e a : K) = star (a : K) := fun a => rfl
  have hN := absNorm_map_equiv e I
  have h1 : I.map (e : 𝓞 K →+* 𝓞 K) ≠ ⊥ := by
    rw [Ne, ← Ideal.absNorm_eq_zero_iff, hN, Ideal.absNorm_eq_zero_iff]
    exact hI
  have := one_le_norm_mul_absNorm c hc (I.map (e : 𝓞 K →+* 𝓞 K) * I) (mul_ne_zero h1 hI) (by
    intro a ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro m hm n hn
      obtain ⟨m', hm', rfl⟩ := (Ideal.mem_map_iff_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective).mp hm
      obtain ⟨o, ho⟩ := h m' hm' n hn
      refine ⟨o, ?_⟩
      rw [ho, ← he]
      simp
    · rintro x y ⟨o, ho⟩ ⟨o', ho'⟩
      refine ⟨o + o', ?_⟩
      change algebraMap _ K (o + o') = c * algebraMap _ K (x + y)
      rw [map_add, map_add, mul_add]
      exact congrArg₂ (· + ·) ho ho')
  rw [map_mul, hN] at this
  push_cast at this
  rw [sq]
  exact this

theorem dualPack : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (S : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (s : ℕ) (ρ : ι → ℝ), h.IsSymm → (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ a : K, ∏ v, ‖τ v a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) → (∀ v, ∀ x : V, x ≠ 0 → 0 < (τ v (h x x)).re) → Nonempty ι → finrank K (Submodule.span K (S : Set V)) = s → I ≠ ⊥ → (∀ x ∈ I • S, ∀ y ∈ I • S, ∃ o : 𝓞 K, (o : K) = h x y) → (∀ v, 0 < ρ v) → {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v}.Finite ∧ ({x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v}.ncard : ℝ) ≤ 9 ^ (s * Fintype.card ι) * (max 1 ((Ideal.absNorm I : ℝ) * ∏ v, ρ v)) ^ s := by
  intro K V _ _ _ _ _ _ _ _ h ι _ τ S I s ρ hs hτ hN hpos hne hrk hI hint hρ
  obtain ⟨v₀⟩ := hne
  have ha : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    have := hpos v₀ x hx
    simp [h0] at this
  have hnn : ∀ v x, 0 ≤ (τ v (h x x)).re := by
    intro v x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos v x hx).le
  have hreal : ∀ v x, τ v (h x x) = ((τ v (h x x)).re : ℂ) := by
    intro v x
    have h1 : star (h x x) = h x x := hs.eq x x
    have h2 := hτ v (h x x)
    rw [h1] at h2
    exact (Complex.conj_eq_iff_re.mp h2.symm).symm
  obtain ⟨f, e, hf⟩ := exists_diag h hs ha s (Submodule.span K (S : Set V)) hrk.le
  let Φ : V →+ (ι → EuclideanSpace ℂ (Fin s)) :=
    { toFun := fun x v => WithLp.toLp 2 fun i =>
        τ v (f i x) * (Real.sqrt (τ v (h (e i) (e i))).re : ℂ)
      map_zero' := by ext v i; simp
      map_add' := by intro x y; ext v i; simp [add_mul] }
  have hΦ : ∀ x ∈ S, ∀ v, ‖Φ x v‖ ^ 2 = (τ v (h x x)).re := by
    intro x hx v
    rw [EuclideanSpace.norm_sq_eq, hf x (Submodule.subset_span hx), map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖τ v (f i x) * (Real.sqrt (τ v (h (e i) (e i))).re : ℂ)‖ ^ 2 = _
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hnn _ _),
      map_mul, map_mul, hτ, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
      Complex.normSq_eq_norm_sq]
  have hinj : Set.InjOn Φ S := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hpos v₀ (x - y) (sub_ne_zero.mpr hne)
    rw [← hΦ _ (S.sub_mem hx hy), map_sub, hxy] at h1
    simp at h1
  have hIpos : (0 : ℝ) < (Ideal.absNorm I : ℝ) := by
    have : Ideal.absNorm I ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI
    positivity
  have hlow : ∀ x ∈ S, x ≠ 0 → (Ideal.absNorm I : ℝ)⁻¹ ≤ ∏ v, (τ v (h x x)).re := by
    intro x hx hx0
    have h1 := one_le_norm_mul_absNorm_sq (h x x) (ha x hx0) I hI (by
      intro a ha b hb
      obtain ⟨o, ho⟩ := hint _ (Submodule.smul_mem_smul ha hx) _ (Submodule.smul_mem_smul hb hx)
      refine ⟨o, ?_⟩
      rw [ho, ← algebraMap_smul K a x, ← algebraMap_smul K b x]
      simp only [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply]
      change (b : K) * (star (a : K) * h x x) = _
      ring)
    have h2 : |((Algebra.norm ℚ (h x x) : ℚ) : ℝ)| = (∏ v, (τ v (h x x)).re) ^ 2 := by
      rw [← hN, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hreal v x, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs, sq_abs]
    have h3 : 0 ≤ ∏ v, (τ v (h x x)).re := Finset.prod_nonneg fun v _ => hnn v x
    rw [h2, ← mul_pow] at h1
    have h4 : 1 ≤ (∏ v, (τ v (h x x)).re) * (Ideal.absNorm I : ℝ) :=
      (one_le_sq_iff₀ (by positivity)).mp h1
    rw [inv_eq_one_div, div_le_iff₀ hIpos]
    exact h4
  obtain ⟨hfin, hcard⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.boxCount ι s (S.toAddSubgroup.map Φ)
    (Ideal.absNorm I : ℝ)⁻¹ (fun v => Real.sqrt (ρ v)) (inv_pos.mpr hIpos)
    (fun v => Real.sqrt_pos.mpr (hρ v)) (by
      rintro _ ⟨x, hx, rfl⟩ hx0
      have hx0' : x ≠ 0 := by rintro rfl; exact hx0 (map_zero Φ)
      rw [Finset.prod_congr rfl fun v _ => hΦ x hx v]
      exact hlow x hx hx0')
  have hset : {x | x ∈ S.toAddSubgroup.map Φ ∧ ∀ v, ‖x v‖ ≤ Real.sqrt (ρ v)}
      = Φ '' {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨x, ⟨hx, fun v => ?_⟩, rfl⟩
      rw [← hΦ x hx v]
      exact (Real.le_sqrt (norm_nonneg _) (hρ v).le).mp (hy v)
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, fun v => ?_⟩
      apply Real.le_sqrt_of_sq_le
      rw [hΦ x hx v]
      exact hy v
  have hinj' : Set.InjOn Φ {x | x ∈ S ∧ ∀ v, (τ v (h x x)).re ≤ ρ v} :=
    hinj.mono fun x hx => hx.1
  rw [hset] at hfin hcard
  refine ⟨Set.Finite.of_finite_image hfin hinj', ?_⟩
  rw [hinj'.ncard_image, Finset.prod_congr rfl fun v _ => Real.sq_sqrt (hρ v).le,
    div_inv_eq_mul, mul_comm (∏ v, ρ v)] at hcard
  exact hcard

end GlobalTheory.DefinitePacking
