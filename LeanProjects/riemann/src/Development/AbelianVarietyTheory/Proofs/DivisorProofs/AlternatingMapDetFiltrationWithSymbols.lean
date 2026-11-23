import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.FiltDet

theorem alt_linComb {E A' : Type} [Field E] [AddCommGroup A'] [Module E A'] {d : ℕ}
    (ω : A' [⋀^Fin d]→ₗ[E] E) (z : Fin d → A') (N : Fin d → Fin d → E) :
    ω (fun j => Fintype.linearCombination E z (N j)) = (Matrix.of N).det * ω z := by
  classical
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun E (Fin d))
    (ω.compLinearMap (Fintype.linearCombination E z))
  have e1 : (fun i => Fintype.linearCombination E z (Pi.basisFun E (Fin d) i)) = z := by
    funext i; simp [Fintype.linearCombination_apply_single]
  have h2 : ω (fun j => Fintype.linearCombination E z (N j)) =
      (ω.compLinearMap (Fintype.linearCombination E z)) N := rfl
  rw [h2, h, AlternatingMap.smul_apply, Pi.basisFun_det,
    AlternatingMap.compLinearMap_apply, e1, smul_eq_mul, mul_comm]
  rfl

theorem det_filtration_symbols : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → ∀ [FiniteDimensional E (U r)], Module.finrank E (U r) ≤ J.card → ∀ (z : Fin d → A') (hz : ∀ q, z (ix q) ∈ U q.1), (∀ q, sym q.1 ⟨z (ix q), hz q⟩ = Pi.single q.2 1) → (∀ k, k ∉ Set.range ix → z k = v k) → ∀ ω : A' [⋀^Fin d]→ₗ[E] E, ω v = (∏ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det) * ω z := by
  intro E A' _ _ _ r d I _ _ U sym hdec hsym ix J v hv hJ _ hcard z hz hzs hzv ω
  classical

  have step : ∀ (a : Fin r) (x : A') (hx : x ∈ U a),
      x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U (a + 1) := by
    intro a x hx
    have hzs' : ∀ i, sym a ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ = Pi.single i 1 := fun i => hzs ⟨a, i⟩
    have hmem : ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz ⟨a, i⟩)
    have hy : x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a := Submodule.sub_mem _ hx hmem
    refine (hsym a ⟨_, hy⟩).1 ?_
    have : (⟨_, hy⟩ : U a) = ⟨x, hx⟩ - ∑ i, sym a ⟨x, hx⟩ i • ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ := by
      ext; simp
    rw [this, map_sub, map_sum]
    simp only [map_smul, hzs']
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨β, hβix, hβout⟩ : ∃ β : Fin d → ℕ, (∀ q, β (ix q) = q.1) ∧
      (∀ k, k ∉ Set.range ix → β k = r) := by
    refine ⟨fun k => if h : k ∈ Set.range ix then ((Classical.choose h).1 : ℕ) else r, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      simp only [dif_pos h]
      rw [ix.injective (Classical.choose_spec h)]
    · intro k hk; simp only [dif_neg hk]
  have hβle : ∀ k, β k ≤ r := by
    intro k
    by_cases hk : k ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hk; rw [hβix]; exact q.1.isLt.le
    · rw [hβout k hk]
  have conv : ∀ (S : Set (Fin d)) (x : A'), x ∈ Submodule.span E (z '' S) →
      ∃ c : Fin d → E, (∀ k ∉ S, c k = 0) ∧ Fintype.linearCombination E z c = x := by
    intro S x hx
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hx
    refine ⟨l, fun k hk => (Finsupp.mem_supported' E l).1 hl k hk, ?_⟩
    rw [Fintype.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  by_cases hli : LinearIndependent E (fun k : J => v k)
  swap
  · have h1 : ¬ LinearIndependent E v := fun h => hli (h.comp _ Subtype.val_injective)
    have h2 : ¬ LinearIndependent E z := by
      intro h; apply hli
      have : (fun k : J => v k) = z ∘ Subtype.val := by
        funext k; exact (hzv k.1 (hJ k.1 k.2).1).symm
      rw [this]; exact h.comp _ Subtype.val_injective
    rw [ω.map_linearDependent v h1, ω.map_linearDependent z h2, mul_zero]
  have hspan : U r ≤ Submodule.span E (Set.range fun k : J => v k) := by
    have hle : Submodule.span E (Set.range fun k : J => v k) ≤ U r := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact (hJ k.1 k.2).2
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
    rw [finrank_span_eq_card hli, Fintype.card_coe]; exact hcard
  have hdown : ∀ n a, a + n = r → U a ≤ Submodule.span E (z '' {k | a ≤ β k}) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      obtain rfl : a = r := by omega
      refine hspan.trans (Submodule.span_mono ?_)
      rintro _ ⟨k, rfl⟩
      refine ⟨k.1, ?_, hzv k.1 (hJ k.1 k.2).1⟩
      simp [hβout k.1 (hJ k.1 k.2).1]
    | succ n ih =>
      intro a ha x hx
      have har : a < r := by omega
      have key := step ⟨a, har⟩ x hx
      have hy := ih (a + 1) (by omega) key
      have hmono : Submodule.span E (z '' {k | a + 1 ≤ β k}) ≤
          Submodule.span E (z '' {k | a ≤ β k}) :=
        Submodule.span_mono (Set.image_mono fun k hk => by
          simp only [Set.mem_setOf_eq] at hk ⊢; omega)
      have hsum : ∑ i, sym ⟨a, har⟩ ⟨x, hx⟩ i • z (ix ⟨⟨a, har⟩, i⟩) ∈
          Submodule.span E (z '' {k | a ≤ β k}) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨ix ⟨⟨a, har⟩, i⟩, ?_, rfl⟩)
        simp [hβix]
      have := Submodule.add_mem _ (hmono hy) hsum
      simpa using this
  have hcol : ∀ q : (Σ a, I a), ∃ col : Fin d → E, Fintype.linearCombination E z col = v (ix q) ∧
      (∀ k, β k < q.1 → col k = 0) ∧
      ∀ i, col (ix ⟨q.1, i⟩) = sym q.1 ⟨v (ix q), hv q⟩ i := by
    rintro ⟨a, i'⟩
    have key := step a (v (ix ⟨a, i'⟩)) (hv ⟨a, i'⟩)
    have hy := hdown (r - (a + 1)) (a + 1) (by omega) key
    obtain ⟨c, hc0, hcL⟩ := conv _ _ hy
    refine ⟨c + ∑ i, sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i • Pi.single (ix ⟨a, i⟩) 1, ?_, ?_, ?_⟩
    · rw [map_add, map_sum, hcL]
      simp only [map_smul, Fintype.linearCombination_apply_single, one_smul]
      abel
    · intro k hk
      have hk' : β k < a := hk
      have h1 : c k = 0 := hc0 k (by simp only [Set.mem_setOf_eq, not_le]; omega)
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h1, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : k ≠ ix ⟨a, i⟩ := by
        rintro rfl; rw [hβix] at hk'; exact lt_irrefl _ hk'
      simp [Pi.single_apply, hne]
    · intro i
      have h1 : c (ix ⟨a, i⟩) = 0 := hc0 _ (by simp [hβix])
      simp [h1, Finset.sum_apply, Pi.single_apply, Sigma.mk.inj_iff]
  choose col hcolL hcol0 hcoldiag using hcol
  obtain ⟨N, hNix, hNout⟩ : ∃ N : Matrix (Fin d) (Fin d) E, (∀ q, N (ix q) = col q) ∧
      (∀ k, k ∉ Set.range ix → N k = Pi.single k 1) := by
    refine ⟨Matrix.of fun k => if h : k ∈ Set.range ix then col (Classical.choose (Set.mem_range.1 h))
      else Pi.single k 1, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      funext j
      simp only [Matrix.of_apply, dif_pos h]
      rw [ix.injective (Classical.choose_spec (Set.mem_range.1 h))]
    · intro k hk; funext j; simp only [Matrix.of_apply, dif_neg hk]
  have hNL : ∀ j, Fintype.linearCombination E z (N j) = v j := by
    intro j
    by_cases hj : j ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hj; rw [hNix]; exact hcolL q
    · rw [hNout j hj, Fintype.linearCombination_apply_single, one_smul]; exact hzv j hj
  have hBT : N.BlockTriangular β := by
    intro i j hij
    by_cases hi : i ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hi; rw [hNix]; exact hcol0 q j (by rw [hβix] at hij; exact hij)
    · rw [hNout i hi, Pi.single_apply, if_neg]; rintro rfl; exact lt_irrefl _ hij
  have hdet : N.det = ∏ a : Fin r,
      (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det := by
    rw [hBT.det]
    have himg : Finset.image β Finset.univ ⊆ Finset.range (r + 1) := by
      intro b hb
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hb
      simp only [Finset.mem_range]; have := hβle k; omega
    rw [Finset.prod_subset himg ?_]
    · rw [Finset.prod_range_succ]
      have hlast : (N.toSquareBlock β r).det = 1 := by
        have : N.toSquareBlock β r = 1 := by
          ext ⟨i, hi⟩ ⟨j, hj⟩
          have hi' : i ∉ Set.range ix := by
            rintro ⟨q, rfl⟩; rw [hβix] at hi; have := q.1.isLt; omega
          rw [Matrix.toSquareBlock_def, Matrix.of_apply, hNout i hi', Pi.single_apply,
            Matrix.one_apply]
          simp only [Subtype.mk.injEq, eq_comm]
        rw [this, Matrix.det_one]
      rw [hlast, mul_one, ← Fin.prod_univ_eq_prod_range (fun x => (N.toSquareBlock β x).det) r]
      refine Finset.prod_congr rfl fun a _ => ?_
      have hinj : Function.Injective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        intro i i' h
        simp only [Subtype.mk.injEq, ix.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at h
        exact h
      have hsurj : Function.Surjective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        rintro ⟨k, hk⟩
        by_cases hkr : k ∈ Set.range ix
        · obtain ⟨⟨b, i⟩, rfl⟩ := hkr
          rw [hβix] at hk
          have hab : b = a := Fin.ext hk
          subst hab
          exact ⟨i, rfl⟩
        · rw [hβout k hkr] at hk; have := a.isLt; omega
      let e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
      show (N.toSquareBlock β a).det = _
      rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
      congr 1
      ext i i'
      show N (ix ⟨a, i'⟩) (ix ⟨a, i⟩) = _
      rw [hNix]
      exact hcoldiag ⟨a, i'⟩ i
    · intro b _ hb
      haveI : IsEmpty {i // β i = b} :=
        ⟨fun ⟨i, hi⟩ => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
      exact Matrix.det_isEmpty
  have hv' : v = fun j => Fintype.linearCombination E z (N j) := funext fun j => (hNL j).symm
  rw [show ω v = ω (fun j => Fintype.linearCombination E z (N j)) from congrArg _ hv',
]
  refine (alt_linComb ω z N).trans ?_
  rw [← hdet]
  rfl

end GlobalTheory.FiltDet
