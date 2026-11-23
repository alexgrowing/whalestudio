import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_sum {Γ A ι : Type} [TopologicalSpace Γ] [AddCommMonoid A] (s : Finset ι) (f : ι → Γ → A)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun g => ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : A)
  | insert a s ha ih =>
    have e : (fun g => ∑ i ∈ insert a s, f i g) = f a + fun g => ∑ i ∈ s, f i g := by
      funext g
      simp [Finset.sum_insert ha]
    rw [e]
    exact (h a).add ih

theorem UpperTheory.V.Ws.Lab.contConj :
    ∀ (Γ R : Type) [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (r : Γ → M4 R) (p q : M4 R), (∀ i j, AdicCont I fun g => r g i j) →
      ∀ i j, AdicCont I fun g => (p * r g * q : M4 R) i j := by
  intro Γ R _ _ I r p q hr i j N
  have e : (fun g => (Ideal.Quotient.mk (I ^ N)) ((p * r g * q : M4 R) i j)) =
      fun g => ∑ k : Fin 4, ∑ m : Fin 4,
        (Ideal.Quotient.mk (I ^ N) (p i m) * Ideal.Quotient.mk (I ^ N) (r g m k)) * Ideal.Quotient.mk (I ^ N) (q k j) := by
    funext g
    simp [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul]
  rw [e]
  refine lc_sum _ _ (fun k => ?_)
  refine lc_sum _ _ (fun m => ?_)
  exact (hr m k N).comp (fun x => (Ideal.Quotient.mk (I ^ N) (p i m) * x) * Ideal.Quotient.mk (I ^ N) (q k j))
