import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_tri {R : Type} [CommRing R] {A : M4 R} (h : IsUp A) : (adj A).BlockTriangular id := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem adj_dg {R : Type} [CommRing R] (A : M4 R) (i : Fin 4) : adj A i i = A i.rev i.rev := by
  rw [adj_apply]
  fin_cases i <;> simp [sgn]

theorem UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair a P → ∀ (v : Φ.ι) (i : Fin 4), P.ψ v i 1 = 1 ∧ (∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t) ∧ ∀ s ∈ Φ.Gv v, P.ψ v i s * P.ψ v i.rev s = a (Φ.ν s) := by
  intro O Γ _ _ Φ R _ a P hP v i
  have hn : adj (P.n v) * P.n v = 1 := by
    have h := (hP.low v).1
    unfold IsGSp at h
    simpa using h
  have hn' : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.mp hn
  refine ⟨?_, ?_, ?_⟩
  · simp [PD.ψ, hn]
  · intro s hs t ht
    have e : adj (P.n v) * P.r (s * t) * P.n v =
        (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r t * P.n v) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul]
    unfold PD.ψ
    rw [e]
    exact UpperTheory.V.Loc.SpFlag.tri_mul_diag (fun p q h => hP.flag v s hs p q h) (fun p q h => hP.flag v t ht p q h) i
  · intro s hs
    have hB := hP.flag v s hs
    have hg := hP.mult s
    unfold IsGSp at hg
    have e : adj (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r s * P.n v) = a (Φ.ν s) • 1 := by
      rw [UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_adj]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul, ← Matrix.mul_assoc (adj (P.r s)), hg]
      simp [hn]
    have d := UpperTheory.V.Loc.SpFlag.tri_mul_diag (adj_tri hB) (fun p q h => hB p q h) i
    rw [e, adj_dg] at d
    unfold PD.ψ
    rw [mul_comm, ← d]
    simp
