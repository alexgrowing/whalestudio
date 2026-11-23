import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfMemTwistedJacquetKernelUpperUnitriangulaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangularStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePrStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

theorem subquotient_prinSeries_of_hasVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → HasVec ψ π → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Agree ψ ω ∧ IsSubquotient π (prinSeries ω) := by
  intro hBZ k _ _ _ _ n ψ V _ _ π hπ hirr hψ hord hvec
  obtain ⟨v, hv0, hv⟩ := hvec
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  have hx0 : (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) ≠ 0 := by
    intro h
    exact hv0 (GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular k n ψ V π hπ hψ hord v ((Submodule.Quotient.mk_eq_zero _).1 h) hv)
  have hact : ∀ t ∈ torusO k (Fin n), jacB π t (Submodule.Quotient.mk v) =
      (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) := by
    intro t ht
    have hgrp : diagT k (Fin n) t ∈ grp ψ := by
      refine ⟨iwahori_le_KO k _ (diagT_mem_iwahori ht), fun i j hij => ?_⟩
      rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne]
      exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
    have hth : theta ψ (diagT k (Fin n) t) = (torusChar ψ t : ℂ) := by
      rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ (diagT k (Fin n) t) t ht (fun i => by rw [val_diagT, Matrix.diagonal_apply_eq])
        (Or.inr fun i j hij => by rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne'])]
      simp
    rw [UnramFixed.jacB_apply, jacBU_mk, hv _ hgrp, hth]
    have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
      UnramFixed.deltaHalf_torusO k ht
    rw [this]
    simp
  obtain ⟨ω, l, hl0, hω, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) (Submodule.Quotient.mk v) ψ
    (isSmooth_jacB hπ) hl hψ hx0 hact
  exact ⟨ω, fun i => GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hψ i) (hu i),
    fun i u hu' => (hu i u hu').symm,
    SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hω⟩

end GlobalTheory.PsType
