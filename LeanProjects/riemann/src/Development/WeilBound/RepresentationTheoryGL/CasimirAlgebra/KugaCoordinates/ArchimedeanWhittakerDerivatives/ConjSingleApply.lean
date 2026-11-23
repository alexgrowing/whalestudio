import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.ContinuousInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem law_inf (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Cinf E)) (hl : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j, u.val j j = 1) (g : GA E a) :
    f (infGL E a u * g) = ψ (sInf E (sd u.val)) * f g := by
  rw [GlobalTheory.CuspGeneric.tri_law E a ψ f hf (infGL E a u) ?_ ?_ g]
  · congr 2
    rw [sd, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
    have hne : p.1 ≠ p.2 := fun h => by rw [h] at hp'; omega
    rw [infGL_apply, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero, sub_zero, zero_add]
  · intro i j hij
    rw [infGL_apply, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', hl i j hij, map_zero]
    simp
  · intro j
    rw [infGL_apply, hd, Matrix.one_apply_eq, Matrix.one_apply_eq]
    simp

omit [NumberField E] [IsTotallyComplex E] in
theorem inv_upper (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) :
    ∀ i j : Fin a, j < i → (b⁻¹).val i j = 0 := by
  let _ : Invertible b.val := b.invertible
  have h : Matrix.BlockTriangular b.val id := fun i j hij => hb i j hij
  intro i j hij
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular h hij

omit [NumberField E] [IsTotallyComplex E] in
theorem diag_inv (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (i : Fin a) :
    b.val i i * (b⁻¹).val i i = 1 := by
  have h := congrFun (congrFun (Units.mul_inv b) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h1 | h1
    · rw [hb i k h1, zero_mul]
    · rw [inv_upper b hb k i h1, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [NumberField E] [IsTotallyComplex E] in
theorem single_sq (p q : Fin a) (h : p ≠ q) (x : Cinf E) : Matrix.single p q x * Matrix.single p q x = 0 := by
  exact Matrix.single_mul_single_of_ne (h := h.symm) ..

omit [NumberField E] [IsTotallyComplex E] in
theorem conj_single_apply (b c : Matrix (Fin a) (Fin a) (Cinf E)) (p q : Fin a) (x : Cinf E) (i j : Fin a) :
    (b * Matrix.single p q x * c) i j = b i p * x * c q j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_assoc]

omit [NumberField E] [IsTotallyComplex E] in
theorem conj_single_upper (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (p q : Fin a)
    (hpq : p < q) (x : Cinf E) : ∀ i j : Fin a, j ≤ i → (b.val * Matrix.single p q x * (b⁻¹).val) i j = 0 := by
  intro i j hji
  rw [conj_single_apply]
  rcases lt_or_ge p i with h1 | h1
  · rw [hb i p h1]; simp
  rcases lt_or_ge j q with h2 | h2
  · rw [inv_upper b hb q j h2]; simp
  · exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le hpq h2)) (not_lt.2 hji)

omit [NumberField E] [IsTotallyComplex E] in
theorem sd_conj_single (b : GL (Fin a) (Cinf E)) (hb : ∀ i j : Fin a, j < i → b.val i j = 0) (p q : Fin a)
    (hpq : p < q) (x : Cinf E) :
    sd (b.val * Matrix.single p q x * (b⁻¹).val) = if (p : ℕ) + 1 = q then b.val p p * x * (b⁻¹).val q q else 0 := by
  have key : ∀ r : Fin a × Fin a, (r.2 : ℕ) = r.1 + 1 → r ≠ (p, q) →
      (b.val * Matrix.single p q x * (b⁻¹).val) r.1 r.2 = 0 := by
    intro r hr hne
    rw [conj_single_apply]
    rcases lt_or_ge p r.1 with h1 | h1
    · rw [hb _ _ h1]; simp
    rcases lt_or_ge r.2 q with h2 | h2
    · rw [inv_upper b hb _ _ h2]; simp
    · exfalso; apply hne
      have e1 : (r.1 : ℕ) ≤ p := h1
      have e2 : (q : ℕ) ≤ r.2 := h2
      have e3 : (p : ℕ) < q := hpq
      exact Prod.ext (Fin.ext (show (r.1 : ℕ) = p by omega)) (Fin.ext (show (r.2 : ℕ) = q by omega))
  unfold sd
  split_ifs with h
  · rw [Finset.sum_eq_single (p, q)]
    · exact conj_single_apply _ _ _ _ _ _ _
    · intro r hr hne; exact key r (Finset.mem_filter.1 hr).2 hne
    · intro hn; exfalso; apply hn
      exact Finset.mem_filter.2 ⟨Finset.mem_univ (p, q), h.symm⟩
  · apply Finset.sum_eq_zero
    intro r hr
    apply key r (Finset.mem_filter.1 hr).2
    rintro rfl; exact h (Finset.mem_filter.1 hr).2.symm

theorem law_conj (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (b : GL (Fin a) (Cinf E)) (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0)
    (hMu : ∀ i j : Fin a, j ≤ i → (b.val * M * (b⁻¹).val) i j = 0) (t : ℝ) :
    f (infGL E a b * infGL E a (cu M hM t)) = ψ (sInf E (t • sd (b.val * M * (b⁻¹).val))) * f (infGL E a b) := by
  set N := b.val * M * (b⁻¹).val with hN
  have hu : (b * cu M hM t * b⁻¹).val = 1 + t • N := by
    rw [Units.val_mul, Units.val_mul, cu_val, mul_add, mul_one, add_mul, Units.mul_inv, mul_smul_comm,
      smul_mul_assoc]
  have e : infGL E a b * infGL E a (cu M hM t) = infGL E a (b * cu M hM t * b⁻¹) * infGL E a b := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have hl : ∀ i j : Fin a, j < i → (b * cu M hM t * b⁻¹).val i j = 0 := by
    intro i j hij
    rw [hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', hMu i j hij.le, smul_zero, add_zero]
  have hd : ∀ j, (b * cu M hM t * b⁻¹).val j j = 1 := by
    intro j
    rw [hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, hMu j j le_rfl, smul_zero, add_zero]
  rw [e, law_inf ψ f hf _ hl hd, hu]
  congr 3
  unfold sd
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
  have hne : p.1 ≠ p.2 := fun h => by rw [h] at hp'; omega
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hne, zero_add]

end PositivityTheory.Rg.Cz
