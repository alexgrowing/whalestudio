import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SepChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.entry_of_single {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b : ι) :
    (single a a (1 : R) * M * single b b (1 : R) : Matrix ι ι R) a b = M a b := by
  simp

theorem UpperTheory.V.AlgebraTools.lemma_L :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ : Fin n → Γ →* Rˣ), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → (∀ g : Fin n → Γ, (List.ofFn fun i => ((r (g i) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - algebraMap R _ ((ψ i (g i) : Rˣ) : R)).prod = 0) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ z : MonoidAlgebra R Γ, (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z).charpoly.map (residue R) = ∏ i, (X - C (residue R (MonoidAlgebra.lift R R Γ ((Units.coeHom _).comp (ψ i)) z)))) → ∃ (z : MonoidAlgebra R Γ) (g : GL (Fin n) R), (∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z - MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ j)) z)) ∧ (∀ i, (g : Matrix (Fin n) (Fin n) R) * lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) i * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = single i i 1) ∧ ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R) := by
  intro R Γ _ _ _ n r ψ hcard hprod hinj hchar
  obtain ⟨z, hz⟩ := sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hcard hinj
  have hord := ord_ext ((Units.coeHom _).comp r) (fun i => (Units.coeHom R).comp (ψ i)) hprod
  obtain ⟨hcoi, htri, hdiag⟩ := lag_triangular
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i))) z hord hz
  have hne := lag_ne_zero (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) _ hz (hchar z)
  obtain ⟨g, hg⟩ := coi_conj_single _ hcoi hne
  refine ⟨z, g, hz, hg, fun s => ?_⟩
  set e := lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z)
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) with he
  have hρ : MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r)
      (MonoidAlgebra.of R Γ s) = ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    simp [MonoidAlgebra.lift_of]
  have hχ : ∀ i, MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) (MonoidAlgebra.of R Γ s)
      = ((ψ i s : Rˣ) : R) := fun i => by
    simp [MonoidAlgebra.lift_of]
  have hinv : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 :=
    Units.inv_mul g
  have key : ∀ i j, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((g : Matrix (Fin n) (Fin n) R) * (e i * ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * e j)
        * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j := by
    intro i j
    refine (UpperTheory.V.AlgebraTools.entry_of_single (((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j).symm.trans ?_
    rw [← hg i, ← hg j]
    congr 1
    simp only [Units.val_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)), hinv, Matrix.one_mul]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [key, ← hρ, htri _ i j hji]
    simp
  · rw [key, ← hρ, hdiag, Matrix.mul_smul, Matrix.smul_mul, hg i, hχ]
    simp
