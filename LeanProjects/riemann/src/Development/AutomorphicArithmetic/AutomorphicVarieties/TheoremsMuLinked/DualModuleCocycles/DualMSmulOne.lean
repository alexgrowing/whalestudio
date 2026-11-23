import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {n : ℕ}

end SlopeTestRemainingChoices

private theorem dualM_mul_dualM {X : Type} [CommRing X] {n : ℕ} (A B A' B' : Matrix (Fin n) (Fin n) X) :
    dualM A B * dualM A' B' = dualM (A * A') (A * B' + B * A') := by
  ext i j
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem UpperTheory.V.Th.Coc.rel :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G H : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X) (φ : H → G) (ψ : Fin n → H → R) (g : Fin n → H), IsLift x δ (repR x ρ) τ c d → repR x ρ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → d (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → (List.ofFn fun i => dualM (bar X (ρ (φ (g i)))) (d (MonoidAlgebra.single (φ (g i)) 1)) - (TrivSqZeroExt.inl (algebraMap O X (x (ψ i (g i)))) + TrivSqZeroExt.inr (c • δ (ψ i (g i))) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0 := by
  intro O R X _ _ _ _ _ n G H _ x δ ρ τ c d φ ψ g hL h1 h2
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hd1 : d 1 = 0 := by
    have := hL.mul 1 1
    simp only [mul_one, map_one, hbar1, one_mul] at this
    have h' : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h'
  have hrep : ∀ (k : G) (r : R), repR x ρ (MonoidAlgebra.single k r) = x r • ρ k := by
    intro k r
    simp [repR, GDet.repAlg]
  have hs : ∀ r : R, MonoidAlgebra.single (1 : G) r = r • (1 : MonoidAlgebra R G) := by
    intro r
    simp [MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  let Φ : MonoidAlgebra R G →* Matrix (Fin n) (Fin n) (DualNumber X) :=
    { toFun := fun a => dualM (bar X (repR x ρ a)) (d a)
      map_one' := by
        ext i j
        · by_cases hij : i = j <;> simp [dualM, hbar1, Matrix.one_apply, hij]
        · by_cases hij : i = j <;> simp [dualM, hd1, Matrix.one_apply, hij]
      map_mul' := by
        intro a b
        rw [dualM_mul_dualM, hL.mul, map_mul]
        simp [bar, Matrix.map_mul, add_comm] }
  have key := map_list_prod Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i)))
  have hz : Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 := by
    show dualM _ _ = 0
    rw [h1, h2]
    ext i j <;> simp [dualM, bar]
  rw [hz, List.map_ofFn] at key
  rw [key]
  congr 2
  funext i
  show _ = dualM (bar X (repR x ρ (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))) (d (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))
  rw [map_sub, map_sub, hrep, hrep, hs (ψ i (g i)), hL.smul, hd1, map_one, map_one, map_one, one_smul, hbar1]
  ext a b
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
