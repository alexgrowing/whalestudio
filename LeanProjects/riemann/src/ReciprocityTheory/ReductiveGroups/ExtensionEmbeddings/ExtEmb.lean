import Mathlib

noncomputable section
open NumberField IsDedekindDomain Cardinal
open scoped nonZeroDivisors

namespace ReciprocityTheory.ChartRestriction.B3

theorem iop_extEmb {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  let : Algebra R K := f.toAlgebra
  let : Algebra R L := g.toAlgebra
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' R L
  have h1 : #K = #ι := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' v hv hR hK
  have h2 : #L = #κ :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' w hw hR (hKL ▸ hK)
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis w hw
  let e' : Algebra.adjoin R (Set.range v) ≃ₐ[R] Algebra.adjoin R (Set.range w) :=
    (hv.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv R e)).trans hw.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K L e'.toRingEquiv, fun r => ?_⟩
  have hf : f r = algebraMap R K r := rfl
  have hg : g r = algebraMap R L r := rfl
  rw [hf, hg, IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range v)) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  have : e'.toRingEquiv (algebraMap R _ r) = algebraMap R _ r := e'.commutes r
  rw [this, ← IsScalarTower.algebraMap_apply]

end ReciprocityTheory.ChartRestriction.B3
