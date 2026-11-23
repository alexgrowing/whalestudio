import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

theorem block_mul {R : Type} [CommRing R] {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ M i j = 0)
    (hN : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ N i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (M * N) i j = 0 := by
  intro i j
  by_cases h : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h
  · right
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hM i k with h1 | h1
    · rcases hN k j with h2 | h2
      · exact absurd (h1.trans h2) h
      · rw [h2, mul_zero]
    · rw [h1, zero_mul]

theorem block_infGL (y : GL (Fin a) (Cinf E))
    (hy : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (y : Matrix (Fin a) (Fin a) (Cinf E)) i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := by
  intro i j
  by_cases h' : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h'
  · right
    have h := (hy i j).resolve_left h'
    have hij : i ≠ j := fun e => h' (by rw [e])
    change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = 0
    rw [h, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero, zero_add]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0)
    (i j : Fin a) (hij : (i : ℕ) < r ↔ (j : ℕ) < r) (x : Cinf E) (m₁ : GA E r) (m₂ : GA E (a - r)) :
    lieD (toL (Matrix.single i j x)) f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  set m := GlobalTheory.LeviGA.blkGL hr (m₁, m₂)
  set X : Lie E a := toL (Matrix.single i j x)
  have hz : ∀ t : ℝ, chart f.1 m (oneL E a + t • X) = 0 := by
    intro t
    unfold chart
    split_ifs with hu
    · have hyb : ∀ k l : Fin a, ((k : ℕ) < r ↔ (l : ℕ) < r) ∨
          ((hu.unit : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) k l = 0 := by
        intro k l
        rw [hu.unit_spec]
        by_cases hkl : ((k : ℕ) < r ↔ (l : ℕ) < r)
        · exact Or.inl hkl
        · right
          have hne : k ≠ l := fun e => hkl (by rw [e])
          have hs : Matrix.single i j x k l = 0 := by
            rw [Matrix.single_apply]
            rw [if_neg]
            rintro ⟨e1, e2⟩
            exact hkl (by rw [← e1, ← e2]; exact hij)
          change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l + t • Matrix.single i j x k l = 0
          rw [hs, Matrix.one_apply_ne hne, smul_zero, add_zero]
      obtain ⟨p, hp⟩ := GlobalTheory.LeviGA.exists_blkGL hr (m * infGL E a hu.unit)
        (by rw [Units.val_mul]; exact block_mul (GlobalTheory.LeviGA.blkGL_block hr _) (block_infGL _ hyb))
      rw [← hp]
      exact hf p.1 p.2
    · rfl
  have hline : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E a)
    rwa [one_smul] at this
  have hd : HasFDerivAt (chart f.1 m) (fderiv ℝ (chart f.1 m) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_chart f.2 m).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) 0 0 := by
    have e : (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) = fun _ => 0 := funext hz
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem Eop_blkGL_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) →
    ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
      (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hij m₁ m₂
  have k := fun x => lieD_single_blkGL hr f hf i j hij x m₁ m₂
  change (1 / 2 : ℂ) * ((lieS E a i j (atEmb τ 1) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) -
    Complex.I * (lieS E a i j (atEmb τ Complex.I) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) = 0
  rw [lieS_apply, lieS_apply, lie_apply, lie_apply, k, k]
  simp

end GlobalTheory.LeviDeriv

end
