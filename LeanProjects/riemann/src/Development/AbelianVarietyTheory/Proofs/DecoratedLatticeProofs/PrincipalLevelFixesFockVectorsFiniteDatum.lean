import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincipalLevelFock

theorem levW_fix_ptAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ Q, ∀ k ∈ levW R i, ω (1, k) (ptAt R i σ BW f Q) = ptAt R i σ BW f Q := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h Q k hk
  have hr : Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) = 1 := by
    have h2 := hk.2.2
    have e : (R.datWp i R.triv).P.H = ⊥ := rfl
    rw [e] at h2
    exact Subgroup.mem_bot.1 h2
  have hk' : k ∈ levG (Wc D i) (R.βW i) (R.datWp i P) := by
    refine ⟨hk.1, hk.2.1, ?_⟩
    show Formalism.L2.DIV.rTup (R.βW i) (R.datWp i P) (finE (Wc D i) k) ∈ (R.datWp i P).P.H
    rw [hr]; exact Subgroup.one_mem _
  have hchi : levChi (Wc D i) (R.βW i) (R.datWp i P) k = 1 := by
    unfold levChi Formalism.L2.DIV.levFn
    rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one]
    have hs : (R.datWp i P).s = 0 := rfl
    have hq : (R.datWp i P).Q = ∅ := rfl
    rw [hs, hq]
    simp
  have hz := GlobalTheory.ZetaLaw.zeta_law R F i t σ s P cμ cη m ω BW f₀ f c io h k hk'
  rw [hchi] at hz
  have hθ : IsInfFam R.θ := h.1.models.inf
  exact (GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hθ h.2.2.2.2.2.1 _ _ _ _ f
    h.2.2.2.2.2.2.2.2.1 1 (Subgroup.one_mem _) k hk.1 1 hz Q).trans (one_smul ℂ _)

end GlobalTheory.PrincipalLevelFock
