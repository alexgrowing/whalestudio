import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveComplexCoordsPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCoordsPrincipalLevelRangeEqTopStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.PrimIn

theorem principalLevel_rows_bijective_of_parts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), A3.fam3.Ok3 1 → R.WeakCharacterisation F → GlobalTheory.LiftRows.UpInj R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → R.PrincipalLevelBijective F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hOk hW hUp hRow hIn
  have hinj := GlobalTheory.T.injective_complexCoords_principalLevel R F hOk hW hIn
  have htop := GlobalTheory.T.complexCoords_principalLevel_range_eq_top R F hOk hW hUp hRow hIn
  refine ⟨hinj _, fun t => ⟨hinj t, ?_⟩⟩
  rw [htop t, htop _]

end GlobalTheory.PrimIn
