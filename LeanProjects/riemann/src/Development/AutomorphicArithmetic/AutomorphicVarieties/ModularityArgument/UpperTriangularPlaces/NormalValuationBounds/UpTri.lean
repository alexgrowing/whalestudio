import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Z.Win

theorem UpperTheory.V.Keep.upTri :
    UpperTheory.V.Keep.UpTri := by
  intro k _ n M M' B d hd hM hM' hMd hM'd hB
  have key : ∀ m : ℕ, ∀ i j : Fin n, j.val + (n - i.val) = m → j < i → B i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h1 : (B * M) i j = B i j * d j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j, hMd]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with h | h
          · have hv : b.val < j.val := h
            rw [ih (b.val + (n - i.val)) (by omega) i b rfl (h.trans hji), zero_mul]
          · rw [hM b j h, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j) h
      have h2 : (M' * B) i j = d i * B i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i, hM'd]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with h | h
          · rw [hM' i b h, zero_mul]
          · have hv : i.val < b.val := h
            have hb' : b.val < n := b.isLt
            rw [ih (j.val + (n - b.val)) (by omega) b j rfl (hji.trans h), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have h3 : B i j * (d j - d i) = 0 := by
        rw [hB, h2] at h1
        rw [mul_sub, ← h1, mul_comm, sub_self]
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd (hd (sub_eq_zero.mp h)) hji.ne
  intro i j hji
  exact key _ i j rfl hji
