import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CardPieceIrrelevantIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Dim

variable {R : Type*} [CommRing R]

theorem krullDim_quotient_add_one_le {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)

theorem two_le_krullDim_of_chain (p₀ p₁ p₂ : Ideal R) [p₀.IsPrime]
    [p₁.IsPrime] [p₂.IsPrime] (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) :
    ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p₀) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₀, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (le_refl _)⟩
  let b : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₁, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 h₀.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₂, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (h₀.le.trans h₁.le)⟩
  have hab : a < b := h₀
  have hbc : b < c := h₁
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := R) p₀) :=
    ⟨2, ![a, b, c], fun i => by fin_cases i <;> simpa⟩
  have := Order.LTSeries.length_le_krullDim s
  exact_mod_cast this

theorem exists_nat_of_two_le_dim_le {x : WithBot ℕ∞} {D : ℕ} (h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ x)
    (hD : x ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : ∃ d ≤ D, x = ((d + 2 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h2 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have := WithBot.coe_le_coe.1 hD
      exact absurd (top_le_iff.1 this) (ENat.natCast_ne_top _)
    | coe n =>
      have h2' : 2 ≤ n := Nat.cast_le.1 (WithBot.coe_le_coe.1 h2)
      have hD' : n ≤ D + 2 := Nat.cast_le.1 (WithBot.coe_le_coe.1 hD)
      refine ⟨n - 2, by omega, ?_⟩
      rw [show n - 2 + 2 = n by omega]
      rfl

theorem not_dim_strict_lt_bound {x y : WithBot ℕ∞} {D : ℕ} (hx : x = ((D + 2 : ℕ) : WithBot ℕ∞))
    (h : x + 1 ≤ y) (hy : y ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : False := by
  subst hx
  have := h.trans hy
  have h' : (((D + 2 + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((D + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast this
  have h'' : D + 2 + 1 ≤ D + 2 := by exact_mod_cast h'
  omega

end Dim

section Kill

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def i2kill (k : K) : MRing ι →ₐ[ℤ] MRing ι := aeval fun v => if v.1 = k then 0 else X v

theorem i2kill_X (k : K) (v : Σ k, ι k) :
    i2kill k (X v : MRing ι) = if v.1 = k then 0 else X v := by
  simp [i2kill]

theorem i2kill_homog_pos {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) {k : K}
    (hk : a k ≠ 0) : i2kill k s = 0 := by
  rw [i2kill, aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum := hs m hm k
  obtain ⟨i, hi⟩ : ∃ i, m ⟨k, i⟩ ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    exact hk (by rw [← hsum]; exact Finset.sum_eq_zero fun i _ => hne i)
  rw [Finset.prod_eq_zero (i := ⟨k, i⟩) (Finsupp.mem_support_iff.2 hi) (by simp [zero_pow hi]),
    mul_zero]

theorem i2kill_homog_zero {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) {k : K}
    (hk : a k = 0) : i2kill k s = s := by
  conv_rhs => rw [← aeval_X_left_apply s]
  rw [i2kill, aeval_def, aeval_def]
  apply eval₂_congr
  intro v m hv hm
  by_cases h : v.1 = k
  · exfalso
    have hsum := hs m (mem_support_iff.2 hm) k
    rw [hk, Finset.sum_eq_zero_iff] at hsum
    obtain ⟨k', i⟩ := v
    simp only at h
    subst h
    exact (Finsupp.mem_support_iff.1 hv) (hsum i (Finset.mem_univ _))
  · simp [h]

theorem le_comap_kill_of_homogeneous {q : Ideal (MRing ι)} (hq : IsMultiHomogIdeal q) (k : K) :
    q ≤ q.comap (i2kill k) := by
  obtain ⟨S, hS, rfl⟩ := hq
  rw [Ideal.span_le]
  intro s hsS
  obtain ⟨a, ha⟩ := hS s hsS
  rw [SetLike.mem_coe, Ideal.mem_comap]
  by_cases h : a k = 0
  · rw [i2kill_homog_zero ha h]; exact Ideal.subset_span hsS
  · rw [i2kill_homog_pos ha h]; exact zero_mem _

end Kill

theorem comap_kill_variables_le {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hh : IsMultiHomogIdeal q) :
    q.comap (i2kill (ι := ι) 0) ≤ q.comap ((i2kill (ι := ι) 1).comp (i2kill 0)) := by
  intro g hg
  rw [Ideal.mem_comap] at hg
  have h1 := le_comap_kill_of_homogeneous hh 1 hg
  rw [Ideal.mem_comap] at h1
  rw [Ideal.mem_comap, AlgHom.comp_apply]
  exact h1

theorem two_le_krullDim_of_relevant_prime {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hq : IsMultiProjPrime q) : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ q) := by
  obtain ⟨hp, hh, hr⟩ := hq
  obtain ⟨i0, hi0⟩ := hr 0
  obtain ⟨i1, hi1⟩ := hr 1
  have : (q.comap (i2kill (ι := ι) 0)).IsPrime := Ideal.comap_isPrime _ _
  have : (q.comap ((i2kill (ι := ι) 1).comp (i2kill 0))).IsPrime := Ideal.comap_isPrime _ _
  have e00 : i2kill (ι := ι) 0 (X ⟨0, i0⟩) = 0 := by rw [i2kill_X, if_pos rfl]
  have e01 : i2kill (ι := ι) 0 (X ⟨1, i1⟩) = X ⟨1, i1⟩ := by
    rw [i2kill_X, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  have e11 : i2kill (ι := ι) 1 (X ⟨1, i1⟩) = 0 := by rw [i2kill_X, if_pos rfl]
  have m1 : (X ⟨1, i1⟩ : MRing ι) ∈ q.comap ((i2kill (ι := ι) 1).comp (i2kill 0)) := by
    rw [Ideal.mem_comap, AlgHom.comp_apply, e01, e11]
    exact zero_mem _
  have m1' : (X ⟨1, i1⟩ : MRing ι) ∉ q.comap (i2kill (ι := ι) 0) := by
    rw [Ideal.mem_comap, e01]
    exact hi1
  have m0 : (X ⟨0, i0⟩ : MRing ι) ∈ q.comap (i2kill (ι := ι) 0) := by
    rw [Ideal.mem_comap, e00]
    exact zero_mem _
  exact two_le_krullDim_of_chain q _ _ (lt_of_le_of_ne (le_comap_kill_of_homogeneous hh 0) fun h => hi0 (h ▸ m0))
    (lt_of_le_of_ne (comap_kill_variables_le hh) fun h => m1' (h ▸ m1))

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
