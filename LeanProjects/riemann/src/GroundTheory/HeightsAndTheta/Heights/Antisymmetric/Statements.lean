import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

section Objects

variable (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ)

def antisymWeyl (j : ℕ) : Subgroup (Equiv.Perm (T × Fin N)) where
  carrier := {σ | ∀ p, (σ p).1 = p.1 ∧ ((σ p).2.val < j ↔ p.2.val < j)}
  one_mem' := by intro p; simp
  mul_mem' := by
    intro σ ρ hσ hρ p
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact ⟨(hσ (ρ p)).1.trans (hρ p).1, (hσ (ρ p)).2.trans (hρ p).2⟩
  inv_mem' := by
    intro σ hσ p
    have h := hσ (σ⁻¹ p)
    have e : σ (σ⁻¹ p) = p := by simp
    rw [e] at h
    exact ⟨h.1.symm, h.2.symm⟩

def IsBlockSimpleSwap (j : ℕ) (σ : Equiv.Perm (T × Fin N)) : Prop :=
  ∃ (τ : T) (a b : Fin N), b.val = a.val + 1 ∧ (b.val < j ∨ j ≤ a.val) ∧
    σ = Equiv.swap (τ, a) (τ, b)

def antisymDelta : MvPolynomial (T × Fin N) ℝ :=
  ∏ τ : T, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b))

def antisymDegree : ℕ := Fintype.card T * N.choose 2

def antisymSpace (j : ℕ) : Submodule ℝ (MvPolynomial (T × Fin N) ℝ) where
  carrier := {P | P ∈ homogeneousSubmodule (T × Fin N) ℝ (antisymDegree T N + 1) ∧
    ∀ σ, IsBlockSimpleSwap T N j σ → rename σ P = -P}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ => by simp⟩
  add_mem' := by
    rintro P Q ⟨hP, hP'⟩ ⟨hQ, hQ'⟩
    refine ⟨Submodule.add_mem _ hP hQ, fun σ hσ => ?_⟩
    rw [map_add, hP' σ hσ, hQ' σ hσ, neg_add]
  smul_mem' := by
    rintro c P ⟨hP, hP'⟩
    refine ⟨Submodule.smul_mem _ c hP, fun σ hσ => ?_⟩
    rw [map_smul, hP' σ hσ, smul_neg]

def antisymInv (j : ℕ) : Submodule ℝ (MvPolynomial (T × Fin N) ℝ) where
  carrier := {l | l ∈ homogeneousSubmodule (T × Fin N) ℝ 1 ∧
    ∀ σ ∈ antisymWeyl T N j, rename σ l = l}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ => by simp⟩
  add_mem' := by
    rintro P Q ⟨hP, hP'⟩ ⟨hQ, hQ'⟩
    refine ⟨Submodule.add_mem _ hP hQ, fun σ hσ => ?_⟩
    rw [map_add, hP' σ hσ, hQ' σ hσ]
  smul_mem' := by
    rintro c P ⟨hP, hP'⟩
    refine ⟨Submodule.smul_mem _ c hP, fun σ hσ => ?_⟩
    rw [map_smul, hP' σ hσ]

def diagHyperplane (τ : T) (a b : Fin N) : Set (T × Fin N → ℝ) :=
  {x | x (τ, a) = x (τ, b)}

end Objects

def AntisymDivisible.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (P : MvPolynomial (T × Fin N) ℝ), P ∈ antisymSpace T N j →
    (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        ∀ x ∈ O ∩ diagHyperplane T N τ a b, eval x P = 0) →
    ∃ l ∈ antisymInv T N j, P = antisymDelta T N * l

def AntisymStability.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)),
    (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      IsCompact (Om τ a b) ∧ Om τ a b ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ Om τ a b) →
    ∃ C : ℝ, ∀ P ∈ antisymSpace T N j, ∃ l ∈ antisymInv T N j,
      ∀ M : ℝ, 0 ≤ M →
        (∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → ∀ x ∈ Om τ a b, |eval x P| ≤ M) →
        ∀ m, |coeff m (P - antisymDelta T N * l)| ≤ C * M

def AntisymPerturbation.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (hj : 0 < j) (hjN : j < N) (h : MvPolynomial (T × Fin N) ℝ)
    (Kτ : T → Set (T × Fin N → ℝ)),
    (∀ τ : T, IsCompact (Kτ τ) ∧
      Kτ τ ⊆ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩ ∧
      (∃ O : Set (T × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane T N τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩ ⊆ Kτ τ) ∧
      ∀ x ∈ Kτ τ, eval x h = 0) →
    ∃ C : ℝ, ∀ (P : MvPolynomial (T × Fin N) ℝ) (v ε : ℝ), P - v • h ∈ antisymSpace T N j →
      (∀ τ : T, ∀ x ∈ Kτ τ, |eval x P| ≤ ε) →
      ∃ l ∈ antisymInv T N j, ∀ m, |coeff m (P - v • h - antisymDelta T N * l)| ≤ C * ε

section Inhabitants

theorem eval_antisymDelta_eq_zero (T : Type*) [Fintype T] [DecidableEq T] (N : ℕ) {τ : T}
    {a b : Fin N} (hab : a < b) {x : T × Fin N → ℝ} (hx : x ∈ diagHyperplane T N τ a b) :
    eval x (antisymDelta T N) = 0 := by
  have hx' : x (τ, a) = x (τ, b) := hx
  unfold antisymDelta
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ τ)
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_Ioi.2 hab)
  simp [hx']

theorem antisymDelta_mul_vanishes (T : Type*) [Fintype T] [DecidableEq T] (N j : ℕ)
    (l : MvPolynomial (T × Fin N) ℝ) (τ : T) (a b : Fin N) (ha : a.val < j) (hb : j ≤ b.val) :
    ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
      ∀ x ∈ O ∩ diagHyperplane T N τ a b, eval x (antisymDelta T N * l) = 0 := by
  refine ⟨Set.univ, isOpen_univ, ⟨0, Set.mem_univ _, rfl⟩, fun x hx => ?_⟩
  have hab : a < b := Fin.lt_def.2 (lt_of_lt_of_le ha hb)
  rw [map_mul, eval_antisymDelta_eq_zero T N hab hx.2, zero_mul]

lemma Ioi_zero_fin_three : Finset.Ioi (0 : Fin 3) = {1, 2} := by decide
lemma Ioi_one_fin_three : Finset.Ioi (1 : Fin 3) = {2} := by decide
lemma Ioi_two_fin_three : Finset.Ioi (2 : Fin 3) = ∅ := by decide

lemma antisymDelta_fin_one_three :
    antisymDelta (Fin 1) 3 = (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) := by
  rw [antisymDelta, Fin.prod_univ_one, Fin.prod_univ_three, Ioi_zero_fin_three, Ioi_one_fin_three, Ioi_two_fin_three]
  simp only [Finset.prod_pair (show (1 : Fin 3) ≠ 2 by decide), Finset.prod_singleton,
    Finset.prod_empty]
  ring

def antisymSample : MvPolynomial (Fin 1 × Fin 3) ℝ :=
  antisymDelta (Fin 1) 3 * ∑ p : Fin 1 × Fin 3, X p

lemma antisymSample_eq : antisymSample =
    (X (0, 0) - X (0, 1)) * (X (0, 0) - X (0, 2)) * (X (0, 1) - X (0, 2)) *
      (X (0, 0) + X (0, 1) + X (0, 2)) := by
  rw [antisymSample, antisymDelta_fin_one_three, Fintype.sum_prod_type, Fin.sum_univ_one,
    Fin.sum_univ_three]

theorem antisymSample_mem : antisymSample ∈ antisymSpace (Fin 1) 3 2 ∧ antisymSample ≠ 0 := by
  have hX : ∀ p q : Fin 1 × Fin 3, IsHomogeneous ((X p - X q : MvPolynomial (Fin 1 × Fin 3) ℝ)) 1 :=
    fun p q => (isHomogeneous_X ℝ p).sub (isHomogeneous_X ℝ q)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_homogeneousSubmodule, antisymSample_eq]
    have hdeg : antisymDegree (Fin 1) 3 + 1 = 1 + 1 + 1 + 1 := by
      simp [antisymDegree]
    rw [hdeg]
    exact (((hX _ _).mul (hX _ _)).mul (hX _ _)).mul
      (((isHomogeneous_X ℝ _).add (isHomogeneous_X ℝ _)).add (isHomogeneous_X ℝ _))
  · rintro σ ⟨τ, a, b, hab, hblk, rfl⟩
    fin_cases τ
    fin_cases a <;> fin_cases b <;> simp at hab hblk ⊢
    rw [antisymSample_eq]
    simp [Equiv.swap_apply_def]
    ring
  · intro h
    have := congrArg (eval (fun p : Fin 1 × Fin 3 => ((p.2 : ℕ) : ℝ))) h
    rw [antisymSample_eq] at this
    simp at this
    norm_num at this

end Inhabitants

end GroundTheory.Heights₂.Heights
