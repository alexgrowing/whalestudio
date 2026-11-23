import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.ExpChart

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base
open ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix Formalism.QuantumDeterminants
open scoped Matrix.Norms.Operator

def levB (k r : ℕ) (a : Fin (2 * r + k + 1)) : ℕ :=
  if a.val < r then a.val else if a.val ≤ r + k then r else a.val - k

def flipB (k r : ℕ) (a : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if a.val < r ∨ r + k < a.val then ⟨2 * r + k - a.val, by omega⟩ else a

def sgnB (k r : ℕ) (a : Fin (2 * r + k + 1)) : ℂ := if a.val = r + k then -1 else 1

variable {k r : ℕ}

theorem levB_le (a : Fin (2 * r + k + 1)) : levB k r a ≤ 2 * r := by
  have ha := a.isLt
  unfold levB
  split_ifs <;> omega

theorem flipB_val (a : Fin (2 * r + k + 1)) :
    (flipB k r a).val = if a.val < r ∨ r + k < a.val then 2 * r + k - a.val else a.val := by
  unfold flipB
  split_ifs <;> rfl

theorem flipB_flipB (a : Fin (2 * r + k + 1)) : flipB k r (flipB k r a) = a := by
  have ha := a.isLt
  apply Fin.ext
  rw [flipB_val, flipB_val]
  split_ifs <;> omega

theorem Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = flipB k r i then sgnB k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, sgnB, Fin.ext_iff, flipB_val]
  split_ifs <;> first | rfl | omega | norm_num

theorem sgnB_flip (a : Fin (2 * r + k + 1)) : sgnB k r (flipB k r a) = sgnB k r a := by
  have ha := a.isLt
  simp only [sgnB, flipB_val]
  split_ifs <;> first | rfl | omega

theorem Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = sgnB k r i * X (flipB k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply, ite_mul]

theorem mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (flipB k r j) * sgnB k r j := by
  have h : ∀ l, (j = flipB k r l) ↔ (l = flipB k r j) := fun l =>
    ⟨fun h => by rw [h, flipB_flipB], fun h => by rw [h, flipB_flipB]⟩
  simp [Matrix.mul_apply, Hpk_apply, h, mul_ite, sgnB_flip]

theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, flipB_flipB, sgnB_flip, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    unfold sgnB
    split_ifs <;> norm_num
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

theorem Hpk_herm : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = flipB k r i
  · have h' : i = flipB k r j := by rw [h, flipB_flipB]
    rw [if_pos h, if_pos h', h, sgnB_flip]
    unfold sgnB
    split_ifs <;> simp
  · have h' : ¬ i = flipB k r j := fun h' => h (by rw [h', flipB_flipB])
    rw [if_neg h, if_neg h', star_zero]

private lemma levB_add_levB_flipB_eq_two_mul (a : Fin (2 * r + k + 1)) :
    levB k r a + levB k r (flipB k r a) = 2 * r := by
  have ha := a.isLt
  simp only [levB, flipB_val]
  split_ifs <;> omega

theorem isFilB : IsFil (levF (levB k r)) (2 * r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij X hX a b hab
    exact hX a b (by omega)
  · intro i j x y hx hy a b hab
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    by_cases h1 : levB k r c < levB k r a + i + 1
    · rw [hx a c h1, zero_mul]
    · rw [hy c b (by omega), mul_zero]
  · rw [eq_bot_iff]
    intro X hX
    rw [Submodule.mem_bot]
    ext a b
    have := levB_le (k := k) (r := r) b
    exact hX a b (by omega)

theorem isAdjB : IsAdj (levF (levB k r)) (adjH (Hpk k r)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    show Hpk k r * (x * y)ᴴ * Hpk k r = Hpk k r * yᴴ * Hpk k r * (Hpk k r * xᴴ * Hpk k r)
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), Hpk_sq, Matrix.one_mul]
  · show Hpk k r * (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r = 1
    rw [conjTranspose_one, Matrix.mul_one, Hpk_sq]
  · intro x hx
    have hx' : ∀ a b, levB k r b < levB k r a + 0 + 1 → x a b = 0 := hx
    show ∀ a b, levB k r b < levB k r a + 0 + 1 → (Hpk k r * xᴴ * Hpk k r) a b = 0
    intro a b hab
    have h1 := levB_add_levB_flipB_eq_two_mul (k := k) (r := r) a
    have h2 := levB_add_levB_flipB_eq_two_mul (k := k) (r := r) b
    have hz : x (flipB k r b) (flipB k r a) = 0 := hx' _ _ (by omega)
    rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, hz, star_zero, mul_zero, zero_mul]

theorem Nset_eq : Nset k r = grpN (levF (levB k r)) (adjH (Hpk k r)) := by
  ext g
  rw [mem_grpN_iff _ _ Hpk_sq]
  constructor
  · rintro ⟨hU, he, hm⟩
    refine ⟨?_, hU⟩

    have hf : ∀ (j : Fin (2 * r + k + 1)) (a : ℕ) (ha : a < r), j.val + a ≤ 2 * r + k →
        g ⟨2 * r + k - a, by omega⟩ j = if (⟨2 * r + k - a, by omega⟩ : Fin (2 * r + k + 1)) = j
          then 1 else 0 := by
      intro j a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        intro ha hja
        have h1 := congrFun (congrFun hU (eI k r ⟨a, ha⟩)) j
        rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (eI k r ⟨a, ha⟩)] at h1
        · rw [conjTranspose_apply, he ⟨a, ha⟩ _ le_rfl, if_pos rfl, Hpk_mul_apply, Hpk_apply] at h1
          have e1 : flipB k r (eI k r ⟨a, ha⟩) = ⟨2 * r + k - a, by omega⟩ :=
            Fin.ext (by rw [flipB_val]; simp [eI, ha])
          have e2 : sgnB k r (eI k r ⟨a, ha⟩) = 1 := by
            unfold sgnB; rw [if_neg]; simp only [eI]; omega
          rw [e1, e2] at h1
          simpa [eq_comm] using h1
        · intro c _ hc
          rw [conjTranspose_apply]
          by_cases hca : c.val < a
          · have e1 : flipB k r c = ⟨2 * r + k - c.val, by omega⟩ :=
              Fin.ext (by rw [flipB_val, if_pos (Or.inl (by omega))])
            rw [Hpk_mul_apply, e1, ih c.val hca (by omega) (by omega), if_neg, mul_zero, mul_zero]
            intro h; have := congrArg Fin.val h; simp only at this; omega
          · rw [he ⟨a, ha⟩ c (by simp only; omega), if_neg hc, star_zero, zero_mul]
        · simp
    intro a b h
    have hal := a.isLt
    have hbl := b.isLt
    have key : g a b = if a = b then 1 else 0 := by
      unfold levB at h
      by_cases hb : b.val < r
      · have := he ⟨b.val, hb⟩ a (by simp only; split_ifs at h <;> omega)
        exact this
      · by_cases hb2 : b.val ≤ r + k
        · exact hm a b (by omega) hb2 (by split_ifs at h <;> omega)
        · have ha : r + k < a.val ∧ b.val ≤ a.val := by split_ifs at h <;> omega
          have := hf b (2 * r + k - a.val) (by omega) (by omega)
          have e : (⟨2 * r + k - (2 * r + k - a.val), by omega⟩ : Fin (2 * r + k + 1)) = a :=
            Fin.ext (by simp only; omega)
          rwa [e] at this
    rw [Matrix.sub_apply, key, Matrix.one_apply, sub_self]
  · rintro ⟨hF, hU⟩
    have key : ∀ a b, levB k r b ≤ levB k r a → g a b = if a = b then 1 else 0 := fun a b h => by
      have := hF a b (by omega)
      rwa [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at this
    refine ⟨hU, fun a i h => key _ _ ?_, fun i j h1 h2 h3 => key _ _ ?_⟩
    · have := a.isLt
      unfold levB eI; simp only; split_ifs <;> omega
    · unfold levB; split_ifs <;> omega

theorem lieOf_Nset_eq : Formalism.MainNotions.S.lieOf (Nset k r) =
    (lieN (levF (levB k r)) (adjH (Hpk k r)) : Set _) := by
  ext Y
  rw [Nset_eq]
  constructor
  · intro h
    have hd := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
    have h' : ∀ t : ℝ, NormedSpace.exp (t • Y) ∈ grpN (levF (levB k r)) (adjH (Hpk k r)) :=
      fun t => by have := h t; rw [Complex.coe_smul] at this; exact this
    refine mem_lieN.mpr ⟨?_, ?_⟩
    · have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hd
      refine (levF (levB k r) 0).closed_of_finiteDimensional.mem_of_tendsto h2
        (Filter.Eventually.of_forall fun t => (levF (levB k r) 0).smul_mem _ ?_)
      simp only [zero_add, zero_smul, NormedSpace.exp_zero]
      exact (h' t).1
    · have h3 := ((LinearMap.toContinuousLinearMap (adjH (Hpk k r))).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) hd).mul hd
      have h4 : HasDerivAt (fun _ : ℝ => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
          0 0 := hasDerivAt_const _ _
      have h5 := h4.unique (h3.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ((h' t).2).symm))
      simp only [Function.comp, zero_smul, NormedSpace.exp_zero, mul_one,
        LinearMap.coe_toContinuousLinearMap', isAdjB.one, one_mul] at h5
      exact eq_neg_of_add_eq_zero_left h5.symm
  · intro h t
    have := exp_mem_grpN isFilB isAdjB ((lieN _ _).smul_mem t h)
    rw [Complex.coe_smul]; exact this

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
