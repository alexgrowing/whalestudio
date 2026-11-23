import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarThetaRationalExpansion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarThetaRationalExpansionStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RatVacAlg
theorem rational_vacuum_eq_smul_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F ∧
        X.ω t (γ, γ') X.vac = κ • F := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hN hL hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have hI := hX.is
  have hom := hI.weil t
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hx : (GlobalTheory.Grid.ofSgn true A).symm (γ * a) ∈ GfC (GlobalTheory.Grid.neg A) := by
    show (GlobalTheory.Grid.ofSgn true A) ((GlobalTheory.Grid.ofSgn true A).symm (γ * a)) ∈ GfC A
    rw [MulEquiv.apply_symm_apply]
    exact hfa
  obtain ⟨κ₁, F, hF, hκ₁⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hI.isVac hsdS hI.rigW.1 cS cT hom _ hx _ hfa'
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.realPoint_acts_on_vacuum_by_algebraicScalar hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have e1 : X.ω t (γ * a, γ' * a') X.vac = κ₁ • F := hκ₁
  have e2 : X.ω t (γ * a, γ' * a') X.vac = C • X.ω t (γ, γ') X.vac := by
    rw [show ((γ * a, γ' * a') : GA D A × GA D WW) = (γ, γ') * (a, a') from rfl, map_mul, Module.End.mul_apply, hC,
      map_smul]
  have hv : X.vac ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn⟩ := hI.isVac.2.norm
    have h1 := hn p hp
    simp [h0, nrm2] at h1
  have hC0 : C ≠ 0 := by
    rintro rfl
    apply hv
    have h2 := congrArg (X.ω t (a, a')⁻¹) hC
    rw [zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact h2
  refine ⟨C⁻¹ * κ₁, F, hF, ?_⟩
  rw [mul_smul, ← e1, e2, smul_smul, inv_mul_cancel₀ hC0, one_smul]
end GlobalTheory.RatVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F ∧
        X.ω t (γ, γ') X.vac = κ • F := by
  first | exact @_root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination | exact _root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination | (intros; apply _root_.GlobalTheory.RatVacAlg.rational_vacuum_eq_smul_algebraic_combination <;> assumption)
end
