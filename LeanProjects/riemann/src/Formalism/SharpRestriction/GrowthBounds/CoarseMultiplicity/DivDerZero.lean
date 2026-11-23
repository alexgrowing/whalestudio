import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CthMonomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section Y

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem ycond_op (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (j : ℕ) {M M' : WithTop ℤ} (n : ℕ)
    (hM : M + ((n : ℤ) : WithTop ℤ) ≤ M') (al be : Fin N × Fin r →₀ ℕ)
    (hn : vecDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} al +
      covDeg (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} be ≤ n)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YCond (KK O) (r := r) LL j M) :
    monomial al 1 * divDer be y ∈ YCond (KK O) (r := r) LL' j M' := by
  cases M' with
  | top => rw [PolBridge.ycond_top]; exact Submodule.mem_top
  | coe M' =>
    cases M with
    | top => simp at hM
    | coe M =>
      rw [PolBridge.mem_ycond_iff D] at hy ⊢
      rw [hv]
      have h1 := flt_op_lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y al be n hn
      refine h1.trans ?_
      have h2 : M + (n : ℤ) ≤ M' := by exact_mod_cast hM
      calc lam1S (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} y + ((n : ℤ) : WithBot ℤ)
          ≤ ((M : ℤ) : WithBot ℤ) + ((n : ℤ) : WithBot ℤ) := by gcongr
        _ = ((M + (n : ℤ) : ℤ) : WithBot ℤ) := by norm_cast
        _ ≤ _ := by exact_mod_cast h2

theorem divDer_zero {R : Type} [CommSemiring R] {σ : Type} (F : MvPolynomial σ R) : divDer 0 F = F := by
  unfold divDer
  conv_rhs => rw [F.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem intPol_cth {σ : Type} (v : σ) (n : ℕ) {y : MvPolynomial σ (KK O)} (hy : y ∈ IntPol O σ) :
    cth v n y ∈ IntPol O σ := by
  rw [mem_integral_poly_iff_coeff] at hy ⊢
  intro m
  obtain ⟨o, ho⟩ := hy m
  exact ⟨o * (((m v).choose n : ℕ) : O), by rw [coeff_cth, ho, map_mul, map_natCast]⟩

theorem intPol_mul {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (hy : y ∈ IntPol O σ) :
    x * y ∈ IntPol O σ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

theorem intPol_X {σ : Type} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntPol O σ := ⟨X v, by simp⟩

theorem yjtZ_cth (D : Formalism.BasicNotions.D7) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : Fin N × Fin r)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    cth v n y ∈ YjtZ O (r := r) LL J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_cth v n hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    apply hy1
    rw [Finset.mem_coe, mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [coeff_cth, h0, zero_mul])
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    refine ycond_op D LL LL rfl (J k) n (hthr k) _ _ ?_ (hy2 k)
    by_cases hn : n = 0
    · subst hn; simp [vecDeg, covDeg]
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ hn, Finset.sum_singleton, Finsupp.single_eq_same]
      split_ifs with h1 h2 <;> first | omega | (exfalso; simp_all)

theorem yjtZ_X (D : Formalism.BasicNotions.D7) (LL LL' : ChainLetters N) (hv : LL'.vec = LL.vec) (a : Fin N) (c : Fin r)
    (hd : ∀ i, LL'.deg i = LL.deg i + if i = a then 1 else 0)
    {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (n : ℕ) (hn : LL.vec a = true → 1 ≤ n)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) :
    X (a, c) * y ∈ YjtZ O (r := r) LL' J thr' := by
  classical
  obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
  refine ⟨⟨?_, ?_⟩, intPol_mul (intPol_X _) hy3⟩
  · unfold chPol Formalism.MainNotions.G.Pol at hy1 ⊢
    rw [SetLike.mem_coe, mem_restrictSupport_iff] at hy1 ⊢
    intro m hm
    rw [Finset.mem_coe, support_X_mul, Finset.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    have h0 := hy1 hm0
    intro i
    have h1 := h0 i
    simp only [multideg, addLeftEmbedding_apply, Finsupp.add_apply] at h1 ⊢
    rw [Finset.sum_add_distrib, h1, hd i, add_comm]
    congr 1
    by_cases hi : i = a
    · subst hi
      simp [Finsupp.single_apply]
    · have : ∀ x : Fin r, (Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ) (i, x) = 0 := by
        intro x
        rw [Finsupp.single_apply, if_neg]
        intro h
        exact hi (congrArg Prod.fst h).symm
      simp [this, hi]
  · rw [SetLike.mem_coe, Submodule.mem_iInf] at hy2 ⊢
    intro k
    have h := ycond_op D LL LL' hv (J k) n (hthr k) (Finsupp.single (a, c) 1) 0 ?_ (hy2 k)
    · rwa [divDer_zero] at h
    · simp only [vecDeg, covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, Finsupp.support_zero, Finset.sum_empty, add_zero]
      split_ifs with h1
      · exact hn h1.2
      · omega

end Y

end Formalism.MainNotions.ColumnSystems.Pf
