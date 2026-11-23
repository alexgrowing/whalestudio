import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dblMat {K H : Type} [Field K] [TopologicalSpace K] [Group H] [TopologicalSpace H] {n : ℕ}
    (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K)
    (hy : ∀ g h, y (g * h) = y g + Loc.adGL ρ g (y h)) : H →* Matrix (Fin (n + n)) (Fin (n + n)) K where
  toFun g := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K))
  map_one' := by
    have h1 : y 1 = 0 := by
      have := hy 1 1
      simpa using this
    simp only [map_one, Units.val_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
  map_mul' g h := by
    rw [← map_mul, Matrix.fromBlocks_multiply, hy]
    congr 2
    · simp
    · simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Units.val_mul,
        Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
      exact add_comm _ _
    · simp
    · simp

theorem UpperTheory.V.Ws.Eb.dblRep :
    ∀ {K H : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ} (ρ : H →* GL (Fin n) K), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ),
        ∃ ρ₂ : H →* GL (Fin (n + n)) K, Continuous ρ₂ ∧ (∀ g, (W.mat ρ₂ g).charpoly = (W.mat ρ g).charpoly ^ 2) ∧ ∀ g, ρ₂ g = 1 → y g = 0 := by
  intro K H _ _ _ _ _ _ n ρ hρ y hy
  obtain ⟨hyc, hyco⟩ := hy
  let D := dblMat ρ y hyco
  have hρv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) K)) := Units.continuous_val.comp hρ
  have hblk : Continuous (fun g => Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
      (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)) :=
    Continuous.matrix_fromBlocks hρv (hyc.matrix_mul hρv) continuous_const hρv
  have hDc : Continuous (fun g => D g) := by
    have e : (fun g => D g) = fun g => (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
        (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g
      rfl
    rw [e]
    exact hblk.matrix_submatrix _ _
  refine ⟨D.toHomUnits, ?_, ?_, ?_⟩
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hDc
    · have e : (fun g => ((D.toHomUnits g)⁻¹ : GL (Fin (n + n)) K).val) = fun g => D g⁻¹ := by
        funext g
        rw [← map_inv, MonoidHom.coe_toHomUnits]
      rw [e]
      exact hDc.comp continuous_inv
  · intro g
    show (D g).charpoly = ((ρ g : Matrix (Fin n) (Fin n) K)).charpoly ^ 2
    simp only [D, dblMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
      Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, pow_two]
  · intro g hg
    have h1 : D g = 1 := by
      rw [← MonoidHom.coe_toHomUnits D g, hg, Units.val_one]
    have h2 : Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K))
        0 (ρ g : Matrix (Fin n) (Fin n) K) = Matrix.fromBlocks 1 0 0 1 := by
      rw [Matrix.fromBlocks_one]
      apply (Matrix.reindexAlgEquiv K K finSumFinEquiv).injective
      rw [map_one]
      exact h1
    obtain ⟨-, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    calc y g = y g * (ρ g : Matrix (Fin n) (Fin n) K) * ((ρ g)⁻¹ : GL (Fin n) K) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hB, Matrix.zero_mul]
