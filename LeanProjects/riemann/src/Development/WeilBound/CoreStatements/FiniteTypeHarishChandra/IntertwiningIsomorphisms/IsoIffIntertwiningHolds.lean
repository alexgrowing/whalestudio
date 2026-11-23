import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDimensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardParabolicSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquarefreeDimensionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyFormulaAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsomorphismPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConsequenceOfMackeyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirrorPartitionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodWordCount
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClauseAToL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem isIrr_of_simple (τ : FDRep ℂ Γ) [h : Simple τ] : IsIrr τ.ρ := (GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 h

theorem zIdemIdemCentral_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (hτ : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.central_idempotent_properties.1 Γ τ hτ

theorem zIdemOrthogonal_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ)
    (h : ¬ Nonempty (τ ≅ σ)) : zIdem τ * zIdem σ = 0 := GlobalTheory.T.central_idempotent_properties.2.1 Γ τ σ hτ hσ h

end Gen

section GeneralLinearIntegers

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem CuspIso.symm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) : CuspIso K mu lam :=
  (GlobalTheory.T.cuspidal_isomorphism_properties K α β β lam lam mu mu (Equiv.refl α |>.trans (Classical.choose h))).1 h

theorem CuspIso.trans {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
    [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} {nu : FDRep ℂ (GL γ K)}
    (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu :=
  (GlobalTheory.T.cuspidal_isomorphism_properties K α β γ lam lam mu nu (Classical.choose h)).2.1 h h'

variable (K) in
theorem mackey_cuspidal : MackeyCusp K := GlobalTheory.T.mackey_formula_all K

variable (K) in
theorem supportUnique_of_mackey (h : MackeyCusp K) : SupportUnique K := (GlobalTheory.T.consequence_of_mackey K h).1

variable (K) in
theorem HC.hcSupportExists_holds : HC.HCSupportExists K := GlobalTheory.T.cuspidal_support_exists K

variable (K) in
theorem A2.sqfreeCore_of (h : MackeyCusp K) : SqfreeCore K :=
  ⟨(GlobalTheory.T.consequence_of_mackey K h).2.1, GlobalTheory.T.squarefree_dimension_formula K, (GlobalTheory.T.consequence_of_mackey K h).2.2⟩

variable (K) in
theorem HCLabelO_mirror (C : LabelConv K) (O : LabelMap K C) : HCLabelO O :=
  (GlobalTheory.T.mirror_partitions K C O (HC.hcSupportExists_holds K) (supportUnique_of_mackey K (mackey_cuspidal K))
    (A2.sqfreeCore_of K (mackey_cuspidal K))).1

end GeneralLinearIntegers

end ReciprocityTheory.Ty.Fin
