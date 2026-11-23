import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

namespace PositivityTheory.RgJS

namespace AbsoluteRigidity

variable {W : Type} {q : W → ℕ} {X : Type} {d : X → ℕ} {A : ∀ x, W → Fin (d x) → ℂ}

theorem rel_symm {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) : Rel q A y x := fun w k => (h w k).symm

def sh (τ : ℝ) (p : X × ℝ) : X × ℝ := (p.1, p.2 - τ)

theorem rel_shift (hq : ∀ w, 2 ≤ q w) {ι κ : Type} [Fintype ι] [Fintype κ] {x : ι → X × ℝ} {y : κ → X × ℝ}
    (h : Rel q A x y) (τ : ℝ) : Rel q A (sh τ ∘ x) (sh τ ∘ y) := by
  intro w k
  have hq0 : (q w : ℂ) ≠ 0 := by
    have := hq w
    exact_mod_cast (by omega : q w ≠ 0)
  have e : ∀ (a : ℂ) (t : ℝ), (a * (q w : ℂ) ^ (-((t - τ : ℝ) : ℂ))) ^ k =
      ((q w : ℂ) ^ (τ : ℂ)) ^ k * (a * (q w : ℂ) ^ (-(t : ℂ))) ^ k := by
    intro a t
    rw [← mul_pow]
    congr 1
    rw [show (q w : ℂ) ^ (τ : ℂ) * (a * (q w : ℂ) ^ (-(t : ℂ))) = a * ((q w : ℂ) ^ (τ : ℂ) * (q w : ℂ) ^ (-(t : ℂ))) by ring,
      ← Complex.cpow_add _ _ hq0]
    congr 2
    push_cast
    ring
  have h1 := congrArg (fun z => ((q w : ℂ) ^ (τ : ℂ)) ^ k * z) (h w k)
  simp only [Finset.mul_sum] at h1
  simp only [Function.comp_apply, sh, e]
  exact h1

theorem rel_remove {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {x : ι → X × ℝ}
    {y : κ → X × ℝ} (h : Rel q A x y) (i : ι) (j : κ) (hij : x i = y j) :
    Rel q A (fun i' : {i' // i' ≠ i} => x i') (fun j' : {j' // j' ≠ j} => y j') := by
  intro w k
  have h1 := h w k
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ j, hij] at h1
  exact add_left_cancel h1

theorem exists_common (hC : Common0) (hS : Sys q X d A) {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ) (h : Rel q A x y) (hne : Nonempty ι ∨ Nonempty κ) :
    ∃ i j, x i = y j := by
  classical
  set T : Finset ℝ := (Finset.univ.image fun i => (x i).2) ∪ (Finset.univ.image fun j => (y j).2) with hT
  have hTne : T.Nonempty := by
    rcases hne with ⟨⟨i⟩⟩ | ⟨⟨j⟩⟩
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
  set τ := T.min' hTne with hτ
  have hx : ∀ i, τ ≤ (x i).2 := fun i =>
    T.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hy : ∀ j, τ ≤ (y j).2 := fun j =>
    T.min'_le _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hmem : τ ∈ T := T.min'_mem hTne
  have hsh := rel_shift hS.primes.two h τ
  have hinj : ∀ p p' : X × ℝ, sh τ p = sh τ p' → p = p' := fun p p' e => by
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [sh] at e1 e2
    exact Prod.ext e1 (by linarith)
  rcases Finset.mem_union.1 hmem with hm | hm
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    obtain ⟨i', j, e⟩ := hC W q X d A hS ι κ (sh τ ∘ x) (sh τ ∘ y) hsh
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      ⟨i, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i', j, hinj _ _ e⟩
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hm
    obtain ⟨j', i, e⟩ := hC W q X d A hS κ ι (sh τ ∘ y) (sh τ ∘ x) (rel_symm hsh)
      (fun j => by simp only [Function.comp_apply, sh]; linarith [hy j])
      (fun i => by simp only [Function.comp_apply, sh]; linarith [hx i])
      ⟨j, by simp only [Function.comp_apply, sh]; linarith⟩
    exact ⟨i, j', (hinj _ _ e).symm⟩

theorem main (hC : Common0) (hS : Sys q X d A) : ∀ (N : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ]
    (x : ι → X × ℝ) (y : κ → X × ℝ), Fintype.card ι + Fintype.card κ ≤ N → Rel q A x y →
      ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
  intro N
  induction N with
  | zero =>
    intro ι κ _ _ x y hN _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by omega)
    have : IsEmpty κ := Fintype.card_eq_zero_iff.1 (by omega)
    exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
  | succ N ih =>
    intro ι κ _ _ x y hN h
    classical
    have step : Nonempty ι ∨ Nonempty κ → ∃ s : ι ≃ κ, ∀ i, x i = y (s i) := by
      intro hne
      obtain ⟨i, j, hij⟩ := exists_common hC hS x y h hne
      have hr := rel_remove h i j hij
      have c1 : Fintype.card {i' // i' ≠ i} < Fintype.card ι := Fintype.card_subtype_lt (p := fun i' => i' ≠ i) (x := i) (by simp)
      have c2 : Fintype.card {j' // j' ≠ j} < Fintype.card κ := Fintype.card_subtype_lt (p := fun j' => j' ≠ j) (x := j) (by simp)
      obtain ⟨s', hs'⟩ := ih {i' // i' ≠ i} {j' // j' ≠ j} (fun i' => x i') (fun j' => y j') (by omega) hr
      refine ⟨(Equiv.optionSubtypeNe i).symm.trans ((Equiv.optionCongr s').trans (Equiv.optionSubtypeNe j)), fun i' => ?_⟩
      by_cases hi : i' = i
      · subst hi
        simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self, Equiv.optionCongr_apply, Option.map_none,
          Equiv.optionSubtypeNe_none]
        exact hij
      · simp only [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi, Equiv.optionCongr_apply, Option.map_some,
          Equiv.optionSubtypeNe_some]
        exact hs' ⟨i', hi⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · rcases isEmpty_or_nonempty κ with hκ | hκ
      · exact ⟨Equiv.equivOfIsEmpty ι κ, fun i => isEmptyElim i⟩
      · exact step (Or.inr hκ)
    · exact step (Or.inl hι)

end AbsoluteRigidity

theorem absolute_rigidity_of_common : Common0 → AbsRig := by
  intro hC W q X d A hS ι κ _ _ x y h
  exact AbsoluteRigidity.main hC hS _ ι κ x y le_rfl h

end PositivityTheory.RgJS
