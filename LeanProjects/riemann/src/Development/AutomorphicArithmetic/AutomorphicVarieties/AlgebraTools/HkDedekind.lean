import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkDedekind :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (f : Perm (Fin n) → K),
      (∀ x : MvPolynomial (Fin n) R, ∑ u, f u * algebraMap _ K (rename u x) = 0) → f = 0 := by
  intro R _ _ n K _ _ _ f hf
  classical
  let φ : Perm (Fin n) → (MvPolynomial (Fin n) R →* K) := fun u =>
    (algebraMap (MvPolynomial (Fin n) R) K).toMonoidHom.comp (rename u : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.toMonoidHom
  have hinj : Function.Injective φ := by
    intro u v huv
    ext i
    have h := DFunLike.congr_fun huv (X i)
    simp only [φ, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_toRingHom, rename_X] at h
    have h2 := IsFractionRing.injective (MvPolynomial (Fin n) R) K h
    exact congrArg Fin.val (X_injective h2)
  have hli := (linearIndependent_monoidHom (MvPolynomial (Fin n) R) K).comp φ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext u
  apply hli f
  funext x
  simpa [φ, Finset.sum_apply] using hf x
