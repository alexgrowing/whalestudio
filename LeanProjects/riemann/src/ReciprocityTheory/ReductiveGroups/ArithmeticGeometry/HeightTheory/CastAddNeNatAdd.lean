import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

namespace ReciprocityTheory.ChartRestriction.G.T0.NPB

open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights

section MH

variable {R : Type*} [CommSemiring R] {B n : ℕ}

theorem isMH_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem isMH_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem isMH_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem isMH_mul_X {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (a + Pi.single i 1) (f * X (i, j)) := by
  classical
  intro s hs b
  rw [support_mul_X, Finset.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  simp only [addRightEmbedding_apply, Finsupp.add_apply, Finset.sum_add_distrib, hf s' hs' b,
    Pi.add_apply]
  congr 1
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [hb]

end MH

theorem countable_mvPoly {σ R : Type*} [Countable σ] [CommSemiring R] [Countable R] :
    Countable (MvPolynomial σ R) := by
  classical
  refine Function.Surjective.countable (f := fun f : (σ →₀ ℕ) →₀ R => f.sum fun m a => monomial m a) ?_
  intro p
  refine ⟨Finsupp.onFinset p.support (fun m => coeff m p) (fun m hm => mem_support_iff.2 hm), ?_⟩
  dsimp only
  rw [Finsupp.onFinset_sum _ (fun m => by simp)]
  exact (MvPolynomial.as_sum p).symm

variable {K : Type} [Field K] {D N : ℕ}

noncomputable def hImg (p : Fin (D + 1) × Fin (N + 1)) :
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  Fin.cases (motive := fun _ => Fin (N + 1) → MvPolynomial (Fin (N + 1 + D))
      (MvPolynomial (Fin D × Fin (N + 1)) K))
    (fun j => X (Fin.castAdd D j)) (fun i j => X (Fin.natAdd (N + 1) i) * C (X (i, j))) p.1 p.2

@[simp] theorem hImg_zero (j : Fin (N + 1)) :
    hImg (K := K) (D := D) ((0 : Fin (D + 1)), j) = X (Fin.castAdd D j) := by
  simp [hImg]

@[simp] theorem hImg_succ (i : Fin D) (j : Fin (N + 1)) :
    hImg (K := K) (i.succ, j) = X (Fin.natAdd (N + 1) i) * C (X (i, j)) := by
  simp [hImg]

noncomputable def homog : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K]
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  aeval hImg

noncomputable def back : MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) →+*
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  eval₂Hom (rename fun p : Fin D × Fin (N + 1) => (p.1.succ, p.2)).toRingHom
    (Fin.addCases (fun j => X (0, j)) (fun _ => 1))

theorem back_homog (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) : back (homog q) = q := by
  have : (back (K := K) (D := D) (N := N)).comp (homog (K := K)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [back, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [back, homog]
      | succ i => simp [back, homog]
  exact congrArg (fun f => f q) this

theorem homog_injective : Function.Injective (homog (K := K) (D := D) (N := N)) :=
  Function.LeftInverse.injective back_homog

theorem castAdd_ne_natAdd (j : Fin (N + 1)) (i : Fin D) : Fin.castAdd D j ≠ Fin.natAdd (N + 1) i := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem homog_coeff_isMH (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    ∀ γ : Fin (N + 1 + D) →₀ ℕ,
    IsMultiHomogeneous (fun i => γ (Fin.natAdd (N + 1) i)) (coeff γ (homog q)) := by
  classical
  induction q using MvPolynomial.induction_on
  · rename_i a
    intro γ
    rw [show homog (C a) = C (C a) from by simp [homog, MvPolynomial.algebraMap_eq], coeff_C]
    split_ifs with h
    · subst h
      intro s hs b
      simpa using isMH_C (B := D) (n := N + 1) a s hs b
    · exact isMH_zero _
  · rename_i p q hp hq
    intro γ
    rw [map_add, coeff_add]; exact isMH_add (hp γ) (hq γ)
  · rename_i p v hp
    intro γ
    obtain ⟨i, j⟩ := v
    rw [map_mul, show homog (X (i, j)) = hImg (K := K) (i, j) from aeval_X _ _]
    cases i using Fin.cases with
    | zero =>
      rw [hImg_zero, coeff_mul_X']
      split_ifs with h
      · have := hp (γ - Finsupp.single (Fin.castAdd D j) 1)
        convert this using 2 with b
        simp [castAdd_ne_natAdd j b]
      · exact isMH_zero _
    | succ i =>
      rw [hImg_succ, ← mul_assoc, mul_comm _ (C (X (i, j))), coeff_C_mul, coeff_mul_X']
      split_ifs with h
      · rw [mul_comm]
        have := isMH_mul_X (hp (γ - Finsupp.single (Fin.natAdd (N + 1) i) 1)) i j
        convert this using 1
        funext b
        have hpos : 1 ≤ γ (Fin.natAdd (N + 1) i) := by
          rw [Finsupp.mem_support_iff] at h; omega
        by_cases hb : b = i
        · subst hb; simp [Finsupp.single_apply]; omega
        · simp [Finsupp.single_apply, Pi.single_apply, hb, Ne.symm hb]
      · rw [mul_zero]; exact isMH_zero _

noncomputable def psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →+* MvPolynomial (Fin (N + 1 + D)) ℂ :=
  (MvPolynomial.map (eval₂Hom sg tt)).comp (homog (K := K)).toRingHom

noncomputable def gpt (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) :
    Fin (D + 1) × Fin (N + 1) → ℂ :=
  fun p => Fin.cases (motive := fun _ => Fin (N + 1) → ℂ) (fun j => y (Fin.castAdd D j))
    (fun i j => y (Fin.natAdd (N + 1) i) * tt (i, j)) p.1 p.2

@[simp] theorem gpt_zero (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (j : Fin (N + 1)) :
    gpt tt y (0, j) = y (Fin.castAdd D j) := by simp [gpt]

@[simp] theorem gpt_succ (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) (i : Fin D)
    (j : Fin (N + 1)) : gpt tt y (i.succ, j) = y (Fin.natAdd (N + 1) i) * tt (i, j) := by simp [gpt]

theorem eval_psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ)
    (q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval y (psi sg tt q) = eval₂ sg (gpt tt y) q := by
  have : (eval y).comp (psi sg tt) = eval₂Hom sg (gpt tt y) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [psi, homog, MvPolynomial.algebraMap_eq]
    · rintro ⟨i, j⟩
      cases i using Fin.cases with
      | zero => simp [psi, homog]
      | succ i => simp [psi, homog]
  exact congrArg (fun f => f q) this

theorem psi_injective (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0) :
    Function.Injective (psi sg tt) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  apply homog_injective (K := K) (D := D) (N := N)
  rw [map_zero]
  refine MvPolynomial.ext _ _ fun γ => ?_
  rw [coeff_zero]
  by_contra hne
  have h0 : coeff γ (psi sg tt q) = 0 := by rw [hq, coeff_zero]
  rw [psi, RingHom.comp_apply, coeff_map] at h0
  exact hG _ _ (homog_coeff_isMH q γ) hne (by simpa using h0)

theorem ae_gen (sg : K →+* ℂ) [Countable K] :
    ∀ᵐ z ∂(blockSphereProb D (N + 1)), ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg (blockPoint z) p ≠ 0 := by
  have := countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro p
  by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
  · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
      fun s hs => hp.1 s (support_map_subset _ _ hs)
    have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
      hp.2 (map_injective sg sg.injective (by rw [h0, map_zero]))
    filter_upwards [ae_blockSphere_eval_ne_zero D (N + 1) a _ hm0 hm] with z hz _ _
    rwa [eval_map] at hz
  · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp

theorem exists_gen (sg : K →+* ℂ) [Countable K] (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0)
    (Q : MvPolynomial (Fin (N + 1 + D)) ℂ) (hQ : Q ≠ 0) :
    ∃ y : Fin (N + 1 + D) → ℂ, eval y Q ≠ 0 ∧
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval₂ sg (gpt tt y) q ≠ 0 := by
  have := countable_mvPoly (σ := Fin (D + 1) × Fin (N + 1)) (R := K)
  have h1 := ae_eval_ne_zero_of_ne_zero_fin _ Q hQ
  have h2 : ∀ᵐ y ∂(volume : Measure (Fin (N + 1 + D) → ℂ)),
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval y (psi sg tt q) ≠ 0 := by
    rw [ae_all_iff]; intro q
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall fun y h => absurd hq h
    · have hq' : psi sg tt q ≠ 0 := fun h0 => hq (psi_injective sg tt hG (by rw [h0, map_zero]))
      filter_upwards [ae_eval_ne_zero_of_ne_zero_fin _ _ hq'] with y hy _ using hy
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  exact ⟨y, hy1, fun q hq => by rw [← eval_psi]; exact hy2 q hq⟩

end ReciprocityTheory.ChartRestriction.G.T0.NPB
