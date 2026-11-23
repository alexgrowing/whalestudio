import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.idemDiag :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (e : Fin n → Matrix (Fin n) (Fin n) O), CompleteOrthogonalIdempotents e → (∀ i, (e i).trace = 1) → ∃ Q : GL (Fin n) O, ∀ i, ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * e i * (Q : Matrix (Fin n) (Fin n) O) = Matrix.single i i 1 := by
  intro O _ _ n e he htr
  classical
  have hmul : ∀ i j, e i * e j = if i = j then e i else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact (he.idem i).eq
    · exact he.ortho hij
  have hentry : ∀ i j a b, (e i * e j) a b = if i = j then e i a b else 0 := by
    intro i j a b
    rw [hmul]
    split_ifs <;> simp
  have hc : ∀ i, ∃ c, IsUnit (e i c c) := by
    intro i
    by_contra hne
    push_neg at hne
    have hmem : (e i).trace ∈ IsLocalRing.maximalIdeal O :=
      Ideal.sum_mem _ (fun c _ => (IsLocalRing.mem_maximalIdeal _).mpr (hne c))
    rw [htr i] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem isUnit_one
  choose c hcu using hc
  let Qm : Matrix (Fin n) (Fin n) O := Matrix.of fun r j => e j r (c j)
  let Sm : Matrix (Fin n) (Fin n) O := Matrix.of fun i r => e i (c i) r
  have hSQ : Sm * Qm = Matrix.diagonal fun i => e i (c i) (c i) := by
    ext i j
    change (e i * e j) (c i) (c j) = _
    rw [hentry, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hdet : IsUnit (Sm * Qm).det := by
    rw [hSQ, Matrix.det_diagonal]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => hcu i)
  rw [Matrix.det_mul] at hdet
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det Qm).mpr (isUnit_of_mul_isUnit_right hdet)
  refine ⟨U, fun i => ?_⟩
  have heQ : e i * Qm = Qm * Matrix.single i i 1 := by
    ext r j
    change (e i * e j) r (c j) = _
    rw [hentry, Matrix.mul_apply]
    simp only [Matrix.single_apply, Qm, Matrix.of_apply]
    split_ifs with h
    · subst h
      simp
    · simp [h]
  rw [mul_assoc, hU, heQ, ← hU, Units.inv_mul_cancel_left]
