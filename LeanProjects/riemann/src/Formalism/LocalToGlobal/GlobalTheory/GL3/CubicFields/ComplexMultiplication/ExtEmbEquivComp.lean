import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical Cardinal
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive)
open Formalism.MainNotions.TaylorLogMetric (lamOf)

theorem extEmb_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).2 f.injective
  haveI : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).2 g.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR (hKL ▸ hK)
  have e : s ≃ t := (Cardinal.eq.1 (h1.symm.trans (hKL.trans h2))).some
  refine ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht, fun r => ?_⟩
  simp only [IsAlgClosed.equivOfTranscendenceBasis]
  rw [show f r = algebraMap R K r from rfl,
    IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap]
  simp [AlgEquiv.commutes]
  rfl

theorem extendEmb_holds : ExtendEmb := by
  intro M hM ρ
  haveI := hM
  have hR : Cardinal.mk M ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ M).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  obtain ⟨σ, hσ⟩ := extEmb_equiv_comp (M.val.toRingHom : M →+* ℂ) (ρ.toRingHom : M →+* ℂ) hR
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) rfl
  exact ⟨σ, fun x => hσ x⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
