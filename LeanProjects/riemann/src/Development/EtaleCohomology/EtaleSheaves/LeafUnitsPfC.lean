import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfB

namespace LateralTheory.E.E4

def LeafNoetherDim : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → ∀ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] B),
  Function.Injective g → g.Finite → s = 1

theorem LeafNoetherCurve_of (hD : LeafNoetherDim) : LeafNoetherCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨s, g, hg, hf⟩ := exists_finite_inj_algHom_of_fg k B
  obtain rfl := hD k B hB s g hg hf
  let e : MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
    (MvPolynomial.finSuccEquiv k 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv k (Fin 0)))
  refine ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective, ?_⟩
  exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e.symm.surjective)

theorem LeafUnitsFG_of_dim (hD : LeafNoetherDim) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_leaves (LeafNoetherCurve_of hD) hV

end LateralTheory.E.E4
