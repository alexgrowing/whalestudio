import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLevelPrincipalFirstBlockIndexEqCardStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem change_of_level_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  intro X Pr R W Ch sel S mu P hX v F' hF
  obtain ⟨ι, hinj, hact, hidx⟩ := GlobalTheory.T.rowLevel_principal_firstBlock_index_eq_card W Ch sel mu P
  have hK := mtildeKOk W Ch sel mu hX
  have hP := mtildeOk W Ch sel mu hX P
  have hf : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D),
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 (g • d)) (F'.1 (g • d)) =
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d) := by
    intro g d
    rw [hF g d]
    exact GlobalTheory.PeriodOnStep.pairAt_rho v _ hP (GlobalTheory.PeriodOnStep.row_act_rat W Ch sel mu P hX) g _
  have hfi : ι.range.FiniteIndex := ⟨by rw [hidx]; exact Nat.card_pos.ne'⟩
  have key := @GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup (mtildeGSD W Ch sel mu P).G (mtildeKGSD W Ch sel mu).G (mtildeGSD W Ch sel mu P).D _ _ _ _ ι hinj hact hfi
    hP.fin_stab (mtildeOk W Ch sel mu hX P).fintypeCl (mtildeKOk W Ch sel mu hX).fintypeCl
    (fun d => (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d)) hf
  rw [hidx] at key
  unfold GSD.ipAt
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeKOk W Ch sel mu hX).fintypeStab _)]
    rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeOk W Ch sel mu hX P).fintypeStab _)]
    rfl

end GlobalTheory
