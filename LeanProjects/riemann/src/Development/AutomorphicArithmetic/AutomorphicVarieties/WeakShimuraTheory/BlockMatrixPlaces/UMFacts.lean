import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private def uMat {R : Type} [CommRing R] (v : Fin 3 → R) : UpperTheory.V.GradeZeroInterpolatingElement.M4 R :=
  !![0, 0, 0, 0; v 0, 0, v 1, 0; 0, 0, 0, 0; v 2, 0, -v 0, 0]

private theorem uMat_mem {R : Type} [CommRing R] (v : Fin 3 → R) : uMat v ∈ uM R := by
  show uMat v ∈ hAB R ⊓ sp4 R
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · show ∀ i j, ¬ lamW i < lamW j → uMat v i j = 0
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [uMat, lamW]
  · show adj (uMat v) = -uMat v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, uMat, Fin.rev]

private theorem uMat_eq {R : Type} [CommRing R] (Y : uM R) : uMat ![Y.1 1 0, Y.1 1 2, Y.1 3 0] = Y.1 := by
  obtain ⟨Y, hY⟩ := Y
  have hA := (Submodule.mem_inf.mp hY).1
  have hS := (Submodule.mem_inf.mp hY).2
  change ∀ i j, ¬ lamW i < lamW j → Y i j = 0 at hA
  change adj Y = -Y at hS
  have h32 := congrFun (congrFun hS 3) 2
  simp [adj_apply, sgn, Fin.rev] at h32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> first
    | exact (hA _ _ (by decide)).symm
    | (rw [h32]; ring)
    | skip

private theorem uMat_add {R : Type} [CommRing R] (v w : Fin 3 → R) : uMat (v + w) = uMat v + uMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> ring

private theorem uMat_smul {R : Type} [CommRing R] (c : R) (v : Fin 3 → R) : uMat (c • v) = c • uMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

private def uEq (R : Type) [CommRing R] : (Fin 3 → R) ≃ₗ[R] uM R where
  toFun v := ⟨uMat v, uMat_mem v⟩
  map_add' v w := Subtype.ext (uMat_add v w)
  map_smul' c v := Subtype.ext (uMat_smul c v)
  invFun Y := ![Y.1 1 0, Y.1 1 2, Y.1 3 0]
  left_inv v := by
    ext i
    fin_cases i <;> rfl
  right_inv Y := Subtype.ext (uMat_eq Y)

theorem UpperTheory.V.Ws.Bl.uMFacts :
    ∀ (R : Type) [CommRing R], Module.Finite R (uM R) ∧ Module.Free R (uM R) ∧ ∀ (I : Ideal R) (Y : uM R), Y ∈ (I • ⊤ : Submodule R (uM R)) ↔ ∀ i j, Y.1 i j ∈ I := by
  intro R _
  refine ⟨Module.Finite.equiv (uEq R), Module.Free.of_equiv (uEq R), ?_⟩
  intro I Y
  constructor
  · intro hY i j
    refine Submodule.smul_induction_on hY ?_ ?_
    · intro r hr n _
      simpa using I.mul_mem_right (n.1 i j) hr
    · intro x y hx hy
      simpa using I.add_mem hx hy
  · intro h
    have hv : (uEq R).symm Y = ∑ k : Fin 3, ((uEq R).symm Y k) • Pi.single k 1 := by
      simpa using ((Pi.basisFun R (Fin 3)).sum_repr ((uEq R).symm Y)).symm
    have hY : Y = ∑ k : Fin 3, ((uEq R).symm Y k) • (uEq R) (Pi.single k 1) := by
      calc Y = uEq R ((uEq R).symm Y) := ((uEq R).apply_symm_apply Y).symm
        _ = _ := by
          conv_lhs => rw [hv]
          rw [map_sum]
          simp only [map_smul]
    rw [hY]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem_smul ?_ Submodule.mem_top)
    fin_cases k
    · exact h 1 0
    · exact h 1 2
    · exact h 3 0
