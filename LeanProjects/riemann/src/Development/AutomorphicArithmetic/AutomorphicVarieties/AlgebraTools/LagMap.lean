import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_map :
    ∀ {R R' E E' ι : Type} [CommRing R] [CommRing R'] [Ring E] [Ring E'] [Algebra R E] [Algebra R' E'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') (π : E →+* E') (a : ι → R) (P : E), (∀ c, π (algebraMap R E c) = algebraMap R' E' (φ c)) → (∀ i j, i ≠ j → IsUnit (a i - a j)) → ∀ i, π (lag a P i) = lag (fun j => φ (a j)) (π P) i := by
  intro R R' E E' ι _ _ _ _ _ _ _ _ φ π a P hc ha i
  have key : ∀ q : R[X], π (aeval P q) = aeval (π P) (q.map φ) := by
    intro q
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext hc
  have hsm : ∀ (c : R) (x : E), π (c • x) = φ c • π x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have h0 := (eq_lag_iff a P i (fun j hj => ha i j (Ne.symm hj)) (lag a P i)).1 rfl
  have h1 := congrArg π h0
  rw [hsm, key] at h1
  simp only [map_prod, Polynomial.map_prod, map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at h1
  rw [eq_lag_iff (fun j => φ (a j)) (π P) i (fun j hj => by
      rw [← map_sub]; exact (ha i j (Ne.symm hj)).map φ) (π (lag a P i))]
  exact h1
