import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHCParamOfSetup

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.LInv

open GlobalTheory.Mom.LowVec

variable {k r : ℕ}

private lemma mEmb_apply_of_not_mem_block (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (h : ¬((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k))) :
    mEmb k r m i j = if i = j then 1 else 0 := by
  simp only [mEmb]
  exact dif_neg h

private lemma mEmb_apply_of_mem_block (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) :
    mEmb k r m i j = m ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ := by
  simp only [mEmb]
  exact dif_pos h

theorem mEmb_mulVec_of_supp (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0) : mEmb k r m *ᵥ v = v := by
  funext i
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : r ≤ i.val
    · rw [hv i hi, mul_zero]
    · rw [mEmb_apply_of_not_mem_block m i i (fun h => hi h.1.1), if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hj : r ≤ j.val
    · rw [hv j hj, mul_zero]
    · rw [mEmb_apply_of_not_mem_block m i j (fun h => hj h.2.1), if_neg (Ne.symm hji), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma mEmb_mul' (m n : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    mEmb k r m * mEmb k r n = mEmb k r (m * n) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [mEmb_apply_of_mem_block (m * n) i j ⟨hi, hj⟩, Matrix.mul_apply]
      let e : Fin (k + 1) ↪ Fin (2 * r + k + 1) := ⟨fun t => ⟨r + t.val, by omega⟩, fun s t h => by
        have h' := congrArg Fin.val h
        exact Fin.ext (by simp only at h'; omega)⟩
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
      · apply Finset.sum_congr rfl
        intro t _
        have ht : (e t).val = r + t.val := rfl
        have h' : (⟨(e t).val - r, by rw [ht]; omega⟩ : Fin (k + 1)) = t :=
          Fin.ext (by show (e t).val - r = t.val; rw [ht]; omega)
        rw [mEmb_apply_of_mem_block m i (e t) ⟨hi, by rw [ht]; omega, by rw [ht]; omega⟩,
          mEmb_apply_of_mem_block n (e t) j ⟨⟨by rw [ht]; omega, by rw [ht]; omega⟩, hj⟩, h']
      · intro l _ hl
        have hl' : ¬(r ≤ l.val ∧ l.val ≤ r + k) := by
          rintro ⟨h1, h2⟩
          apply hl
          exact Finset.mem_map.2 ⟨⟨l.val - r, by omega⟩, Finset.mem_univ _,
            Fin.ext (by show r + (l.val - r) = l.val; omega)⟩
        rw [mEmb_apply_of_not_mem_block m i l (fun h => hl' h.2), if_neg (by rintro rfl; exact hl' hi), zero_mul]
    · rw [mEmb_apply_of_not_mem_block (m * n) i j (fun h => hj h.2)]
      rw [Finset.sum_eq_single j]
      · rw [mEmb_apply_of_not_mem_block n j j (fun h => hj h.1), if_pos rfl, mul_one]
        exact mEmb_apply_of_not_mem_block m i j (fun h => hj h.2)
      · intro l _ hlj
        rw [mEmb_apply_of_not_mem_block n l j (fun h => hj h.2), if_neg hlj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
  · rw [mEmb_apply_of_not_mem_block (m * n) i j (fun h => hi h.1)]
    rw [Finset.sum_eq_single i]
    · rw [mEmb_apply_of_not_mem_block m i i (fun h => hi h.1), if_pos rfl, one_mul]
      exact mEmb_apply_of_not_mem_block n i j (fun h => hi h.1)
    · intro l _ hli
      rw [mEmb_apply_of_not_mem_block m i l (fun h => hi h.1), if_neg (Ne.symm hli), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

private lemma mEmb_one' : mEmb k r (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) = 1 := by
  ext i j
  by_cases h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [mEmb_apply_of_mem_block 1 i j h, Matrix.one_apply, Matrix.one_apply]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg]
      intro h'
      apply hij
      have h'' : i.val - r = j.val - r := congrArg Fin.val h'
      exact Fin.ext (by omega)
  · rw [mEmb_apply_of_not_mem_block 1 i j h, Matrix.one_apply]

theorem isUnit_det_mEmb {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : IsUnit m.det) :
    IsUnit (mEmb k r m).det := by
  have h1 : m * m⁻¹ = 1 := Matrix.mul_nonsing_inv m hm
  have h2 : (mEmb k r m).det * (mEmb k r m⁻¹).det = 1 := by
    rw [← Matrix.det_mul, mEmb_mul', h1, mEmb_one', Matrix.det_one]
  exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h2)

theorem uEmb_diagonal (a : Fin r → ℂ) (ha : ∀ b, a b ≠ 0) :
    ∃ d : Fin (2 * r + k + 1) → ℂ, uEmb k r (Matrix.diagonal a) = Matrix.diagonal d ∧ (∀ i, d i ≠ 0) ∧
      ∀ b, d (eI k r b) = a b := by
  have hinv : (Matrix.diagonal a)⁻¹ = Matrix.diagonal fun b => (a b)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun b => a b * (a b)⁻¹) = fun _ => (1 : ℂ) := funext fun b => mul_inv_cancel₀ (ha b)
    rw [this, Matrix.diagonal_one]
  refine ⟨fun i => if h : i.val < r then a ⟨i.val, h⟩ else
      if h' : r + k < i.val then star ((a ⟨2 * r + k - i.val, by omega⟩)⁻¹) else 1, ?_, ?_, ?_⟩
  · ext i j
    simp only [uEmb]
    rw [hinv]
    by_cases h1 : i.val < r ∧ j.val < r
    · rw [dif_pos h1]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, dif_pos h1.1]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne]
        intro h
        have h2 := congrArg Fin.val h
        exact hij (Fin.ext h2)
    · rw [dif_neg h1]
      by_cases h2 : r + k < i.val ∧ r + k < j.val
      · rw [dif_pos h2]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
            dif_neg (show ¬ i.val < r from fun h => h1 ⟨h, h⟩), dif_pos h2.1]
        · have hne : (2 * r + k - j.val) ≠ (2 * r + k - i.val) := by
            intro h
            apply hij
            exact Fin.ext (by omega)
          rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne, star_zero]
          intro h
          have h2 := congrArg Fin.val h
          exact hne h2
      · rw [dif_neg h2]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, Matrix.diagonal_apply_eq, dif_neg (show ¬ i.val < r from fun h => h1 ⟨h, h⟩),
            dif_neg (show ¬ r + k < i.val from fun h => h2 ⟨h, h⟩)]
        · rw [if_neg hij, Matrix.diagonal_apply_ne _ hij]
  · intro i
    dsimp only
    split_ifs
    · exact ha _
    · rw [Ne, star_eq_zero, inv_eq_zero]
      exact ha _
    · exact one_ne_zero
  · intro b
    dsimp only
    have hb : (eI k r b).val = b.val := rfl
    rw [dif_pos (show (eI k r b).val < r by rw [hb]; exact b.isLt)]
    congr 1

theorem norm_le_eucl {N : ℕ} (v : Fin N → ℂ) (i : Fin N) : ‖v i‖ ≤ eucl v := by
  unfold Formalism.MainNotions.S.eucl
  rw [show ‖v i‖ = Real.sqrt (Complex.normSq (v i)) by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i))

theorem eucl_single {N : ℕ} (i : Fin N) (c : ℂ) : eucl (Pi.single i c : Fin N → ℂ) = ‖c‖ := by
  unfold Formalism.MainNotions.S.eucl
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, Complex.normSq_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem lA_torus (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r → ℝ) (ha : ∀ b, 0 < a b)
    {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : IsUnit m.det) (b : Fin r) :
    lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹ := by
  set g := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg
  obtain ⟨d, hd, hd0, hda⟩ := uEmb_diagonal (k := k) (fun b => (a b : ℂ))
    (fun b => Complex.ofReal_ne_zero.2 (ha b).ne')
  have hgu : IsUnit g.det := by
    rw [hg, Matrix.det_mul, hd, Matrix.det_diagonal]
    exact (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd0 i)).mul (isUnit_det_mEmb hm)
  have key : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ i : Fin (2 * r + k + 1), r ≤ i.val → w i = 0) →
      g⁻¹ *ᵥ w = fun i => w i / d i := by
    intro w hw
    have hu : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (fun i => w i / d i) i = 0 := by
      intro i hi
      simp [hw i hi]
    have hgw : g *ᵥ (fun i => w i / d i) = w := by
      rw [hg, ← Matrix.mulVec_mulVec, mEmb_mulVec_of_supp m hu, hd]
      funext i
      rw [Matrix.mulVec_diagonal]
      show d i * (w i / d i) = w i
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (hd0 i)]
    calc g⁻¹ *ᵥ w = g⁻¹ *ᵥ (g *ᵥ fun i => w i / d i) := by rw [hgw]
      _ = fun i => w i / d i := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hgu, Matrix.one_mulVec]
  have hbi : (Formalism.QuantumDeterminants.eI k r b).val = b.val := rfl
  have hf : Formalism.QuantumDeterminants.fvec k r z b.castSucc = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) := by
    unfold Formalism.QuantumDeterminants.fvec
    rw [dif_pos (show (Fin.castSucc b).val < r from b.isLt)]
    try rfl
  have hsupp : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) i = 0 := by
    intro i hi
    rw [Formalism.QuantumDeterminants.bvec, Pi.single_eq_of_ne]
    intro h
    rw [h] at hi
    omega
  unfold Formalism.MainNotions.S.lA
  simp only [hf]
  apply IsLeast.csInf_eq
  constructor
  · rw [Set.mem_setOf_eq]
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [sub_zero, key _ hsupp]
    have hs : (fun i => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) i / d i) =
        Pi.single (Formalism.QuantumDeterminants.eI k r b) ((a b : ℂ)⁻¹) := by
      funext i
      by_cases hi : i = Formalism.QuantumDeterminants.eI k r b
      · subst hi
        rw [Formalism.QuantumDeterminants.bvec, Pi.single_eq_same, Pi.single_eq_same, hda, one_div]
      · rw [Formalism.QuantumDeterminants.bvec, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, zero_div]
    rw [hs, eucl_single, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha b)]
  · intro t ht
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨y, hy, rfl⟩ := ht
    have hy' := (GlobalTheory.Mom.LowVec.mem_flagSpan).1 hy
    have hw : ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
        (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) - y) i = 0 := by
      intro i hi
      rw [Pi.sub_apply, hy' i (by rw [Fin.coe_castSucc]; omega), hsupp i hi, sub_zero]
    rw [key _ hw]
    have h1 : (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) - y) (Formalism.QuantumDeterminants.eI k r b) = 1 := by
      rw [Pi.sub_apply, hy' _ (by rw [Fin.coe_castSucc]; exact le_of_eq hbi.symm), Formalism.QuantumDeterminants.bvec,
        Pi.single_eq_same, sub_zero]
    calc (a b)⁻¹ = ‖(Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) - y) (Formalism.QuantumDeterminants.eI k r b) / d (Formalism.QuantumDeterminants.eI k r b)‖ := by
          rw [h1, hda, one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha b)]
      _ ≤ _ := norm_le_eucl (fun i => (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b) - y) i / d i) (Formalism.QuantumDeterminants.eI k r b)

theorem lA_nonneg (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) (a : Fin (r + 1)) : 0 ≤ lA k r z x a := by
  unfold Formalism.MainNotions.S.lA
  apply Real.sInf_nonneg
  rintro t ⟨y, _, rfl⟩
  exact Real.sqrt_nonneg _

theorem lengths_basic : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), (∀ a, lA k r z (s * x * κ) a = lA k r z x a) ∧ Sg k r z (s * x * κ) = Sg k r z x) ∧ (∀ (a : Fin r → ℝ), (∀ b, 0 < a b) → ∀ m ∈ UH (Hb k), ∀ b : Fin r, lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹) ∧ (∀ x, 1 ≤ Sg k r z x ∧ (∀ a, 0 ≤ lA k r z x a ∧ lA k r z x a ≤ Sg k r z x) ∧ (Sg k r z x = 1 ∨ ∃ a, Sg k r z x = lA k r z x a)) := by
  intro k r z hz
  refine ⟨?_, ?_, ?_⟩
  · intro x _ s hs κ hκ
    have hl : ∀ a, lA k r z (s * x * κ) a = lA k r z x a := fun a => by
      rw [GlobalTheory.Mom.LowVec.lA_right z (s * x) hκ.2 a, GlobalTheory.Mom.LowVec.lA_left hz hs x a]
    refine ⟨hl, ?_⟩
    unfold GlobalTheory.Amp.Sg
    simp only [hl]
  · intro a ha m hm b
    refine lA_torus z a ha ?_ b
    have hH : (Formalism.QuantumDeterminants.Hb k).det ≠ 0 := by
      unfold Formalism.QuantumDeterminants.Hb
      rw [Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> norm_num
    have hm' : mᴴ * Formalism.QuantumDeterminants.Hb k * m = Formalism.QuantumDeterminants.Hb k := hm
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hH
    rw [← hm', Matrix.det_mul, h0, mul_zero]
  · intro x
    have hle : ∀ a, lA k r z x a ≤ Sg k r z x := fun a => by
      unfold GlobalTheory.Amp.Sg
      exact (Finset.le_fold_max _).2 (Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩)
    have h1 : 1 ≤ Sg k r z x := by
      unfold GlobalTheory.Amp.Sg
      exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
    refine ⟨h1, fun a => ⟨lA_nonneg z x a, hle a⟩, ?_⟩
    have h2 : Sg k r z x ≤ 1 ∨ ∃ a ∈ (Finset.univ : Finset (Fin (r + 1))), Sg k r z x ≤ lA k r z x a := by
      have h3 : Sg k r z x ≤ Sg k r z x := le_rfl
      unfold GlobalTheory.Amp.Sg at h3 ⊢
      exact (Finset.le_fold_max _).1 h3
    rcases h2 with h | ⟨a, _, h⟩
    · exact Or.inl (le_antisymm h h1)
    · exact Or.inr ⟨a, le_antisymm h (hle a)⟩

end GlobalTheory.Amp.LInv
