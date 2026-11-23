import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl

private def blockAdjointFin2 (R : Type) [CommRing R] : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun Y := Matrix.of fun a b => (sgn (ixB a) * sgn (ixB b)) • Y b.rev a.rev
  map_add' X Y := by ext a b; simp only [Matrix.of_apply, Matrix.add_apply, smul_add]
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    rw [smul_comm]

private theorem adjoint_block_submatrix_eq {R : Type} [CommRing R] (X : M4 R) :
    blockAdjointFin2 R (X.submatrix ixA ixA) = (adj X).submatrix ixB ixB := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem adjoint_block_surjective {R : Type} [CommRing R] : Function.Surjective (blockAdjointFin2 R) := by
  intro Y
  refine ⟨blockAdjointFin2 R Y, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockAdjointFin2, ixB, sgn]

end UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.spanB :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R), BG r → Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA) = ⊤ → Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) = ⊤ := by
  intro R Γ _ _ r hr hA
  have hadj : ∀ g, (adj (r g)).submatrix ixB ixB ∈ Submodule.span R (Set.range fun g => (r g).submatrix ixB ixB) := by
    intro g
    obtain ⟨ν, hν⟩ := hr.gsp g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [(grp R).2.2.2.2.2.2.1 ν _ _ hν hinv]
    have hs : (ν • r g⁻¹).submatrix ixB ixB = ν • (r g⁻¹).submatrix ixB ixB := rfl
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
  rw [eq_top_iff]
  calc (⊤ : Submodule R (Matrix (Fin 2) (Fin 2) R))
        = Submodule.map (blockAdjointFin2 R) ⊤ := by
          rw [Submodule.map_top, LinearMap.range_eq_top.mpr adjoint_block_surjective]
    _ = Submodule.map (blockAdjointFin2 R) (Submodule.span R (Set.range fun g => (r g).submatrix ixA ixA)) := by rw [hA]
    _ = Submodule.span R (blockAdjointFin2 R '' Set.range fun g => (r g).submatrix ixA ixA) := Submodule.map_span _ _
    _ ≤ _ := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [adjoint_block_submatrix_eq]
      exact hadj g
