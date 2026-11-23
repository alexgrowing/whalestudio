import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.adicLC :
    ∀ (Γ R : Type) [TopologicalSpace Γ] [CommRing R] (t : R) (m : ℕ) (f : Γ → R), t ^ m = 0 → (AdicCont (Ideal.span {t}) f ↔ IsLocallyConstant f) := by
  intro Γ R _ _ t m f ht
  constructor
  · intro h
    refine IsLocallyConstant.desc f (Ideal.Quotient.mk (Ideal.span {t} ^ m)) (h m) ?_
    intro a b hab
    rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, ht, Ideal.mem_span_singleton, zero_dvd_iff,
      sub_eq_zero] at hab
    exact hab
  · intro h N
    exact h.comp _
