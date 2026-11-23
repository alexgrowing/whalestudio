import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_extend_of_embedding :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  intro Ω _ ε s
  letI : Algebra Ω ℂ := ε.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis Ω ℂ
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let e := hB.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv B s).trans hB.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : ∀ y : Ω,
      algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.C y)) = ε y := fun y => by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  conv_lhs => rw [← h1 x]
  rw [IsAlgClosure.equivOfEquiv_algebraMap, ← h1 (s x)]
  congr 1
  simp [e]

end GlobalTheory.FN
