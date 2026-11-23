import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.RowTypeVec

theorem vec_of_rows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → (∀ i, StdPsi hF (PW i)) → ∀ π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∀ i, ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec ((PW i).ψ ⁻¹' (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))) (fun κ => (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A)))) ((PW i).ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hgen n hF PY PW hPY hPW π hπ i
  obtain ⟨v, hvS, hv0, hvT, hvG⟩ := GlobalTheory.T.exists_good_fixed_vector_of_type_occurring_in_rows R F hOk hC PY π hπ
  obtain ⟨x, hxS, hx0, hxT⟩ := GlobalTheory.T.exists_baseLevel_vector_of_principalLevel_fixed R F hOk hC hgen PY (principalLevelFrame.FinTyp.conjT π) v hvS hv0 hvT hvG
  set y : Formalism.AUTREP.GAf D.host.E n → ℂ := fun g => star (x g) with hy
  have hyS : y ∈ π.S := hxS
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    funext g
    have := congrFun h g
    simpa [hy] using this
  have hyT : principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))))
      (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))) (PY.ψ κ)) y := by
    intro κ hκ
    have e := hxT κ hκ
    funext g
    have eg := congrFun e g
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul] at eg
    simp only [hy, principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, eg, star_mul', GlobalTheory.T.star_rows_level_character_eq_lifts_level_character R F false]
  obtain ⟨h, hh⟩ := GlobalTheory.T.levels_standardFrames_conjugate_standardGroup R F hC i hF PY (PW i) hPY (hPW i) (R.levL F false (sg0 D A))
  refine ⟨Formalism.L2.NG.rt D.host.E n h y, π.stable h y hyS, ?_, ?_⟩
  · intro h0
    apply hy0
    have := congrArg (Formalism.L2.NG.rt D.host.E n h⁻¹) h0
    rwa [principalLevelFrame.rt_rt, inv_mul_cancel, principalLevelFrame.rt_one, map_zero] at this
  · intro κ hκ
    obtain ⟨h1, h2⟩ := hh κ hκ
    have e : κ * h = h * (h⁻¹ * κ * h) := by group
    show Formalism.L2.NG.rt D.host.E n κ (Formalism.L2.NG.rt D.host.E n h y) = _
    rw [principalLevelFrame.rt_rt, e, ← principalLevelFrame.rt_rt, hyT _ h1, map_smul]
    exact congrArg (· • Formalism.L2.NG.rt D.host.E n h y) h2.symm

end GlobalTheory.RowTypeVec

end
