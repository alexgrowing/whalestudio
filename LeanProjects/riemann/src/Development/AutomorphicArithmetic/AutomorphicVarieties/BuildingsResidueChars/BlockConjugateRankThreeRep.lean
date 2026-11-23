import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private def gl2ToGL3BlockMatrix {k : Type} [Field k] (a : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 3) (Fin 3) k :=
  !![a 0 0, 0, a 0 1; 0, 1, 0; a 1 0, 0, a 1 1]

private theorem gl2ToGL3BlockMatrix_mul {k : Type} [Field k] (a b : Matrix (Fin 2) (Fin 2) k) :
    gl2ToGL3BlockMatrix (a * b) = gl2ToGL3BlockMatrix a * gl2ToGL3BlockMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2ToGL3BlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_embedding_one {k : Type} [Field k] :
    gl2ToGL3BlockMatrix (1 : Matrix (Fin 2) (Fin 2) k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl2ToGL3BlockMatrix]

private def gl2ToGL3BlockHom {k : Type} [Field k] : GL (Fin 2) k →* GL (Fin 3) k :=
  Units.map ({ toFun := gl2ToGL3BlockMatrix, map_one' := block_embedding_one, map_mul' := gl2ToGL3BlockMatrix_mul } :
    Matrix (Fin 2) (Fin 2) k →* Matrix (Fin 3) (Fin 3) k)

theorem UpperTheory.block_conjugate_rank_three_rep :
    ∀ (Γ Δ k : Type) [Group Γ] [Group Δ] [Field k] (φ : Γ → Δ) (W W' : Δ →* GL (Fin 2) k) (ρ ρ' : Γ →* GL (Fin 3) k) (g g' : GL (Fin 3) k), (∀ s, ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W (φ s) 0 0, 0, W (φ s) 0 1; 0, 1, 0; W (φ s) 1 0, 0, W (φ s) 1 1]) → (∀ s, ((g' * ρ' s * g'⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = !![W' (φ s) 0 0, 0, W' (φ s) 0 1; 0, 1, 0; W' (φ s) 1 0, 0, W' (φ s) 1 1]) → RepIso W W' → RepIso ρ ρ' := by
  intro Γ Δ k _ _ _ φ W W' ρ ρ' g g' hρ hρ' hWW
  obtain ⟨h, hh⟩ := hWW
  let H : GL (Fin 3) k := gl2ToGL3BlockHom h
  have c : ∀ s, g' * ρ' s * g'⁻¹ = H * (g * ρ s * g⁻¹) * H⁻¹ := by
    intro s
    apply Units.ext
    have e1 : ((H * (g * ρ s * g⁻¹) * H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (H : Matrix (Fin 3) (Fin 3) k) * ((g * ρ s * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          ((H⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [Units.val_mul, Units.val_mul]
    rw [e1, hρ s, hρ' s]
    change gl2ToGL3BlockMatrix ((W' (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      gl2ToGL3BlockMatrix (h : Matrix (Fin 2) (Fin 2) k) * gl2ToGL3BlockMatrix ((W (φ s) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        gl2ToGL3BlockMatrix ((h⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [hh (φ s), Units.val_mul, Units.val_mul, gl2ToGL3BlockMatrix_mul, gl2ToGL3BlockMatrix_mul]
  refine ⟨g'⁻¹ * H * g, fun s => ?_⟩
  calc ρ' s = g'⁻¹ * (g' * ρ' s * g'⁻¹) * g' := by group
    _ = g'⁻¹ * (H * (g * ρ s * g⁻¹) * H⁻¹) * g' := by rw [c s]
    _ = g'⁻¹ * H * g * ρ s * (g'⁻¹ * H * g)⁻¹ := by group
