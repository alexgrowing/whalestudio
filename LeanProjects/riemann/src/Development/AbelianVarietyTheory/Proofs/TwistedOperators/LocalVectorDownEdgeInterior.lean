import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelProdHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtExtDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfGivenFnDown
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFnEqExtDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesSubsetChosenPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem locVec_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}
    (s : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j))
    (hj : (j : ℕ) + 1 < D.R.m) (hg : HEq g (R.vY t j)) (e : AE D) (he : IsIdemSum e (locPl ch.G t)) (Φ : ch.G.Datum) :
    IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) (((1 : ℂˣ) : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  classical
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hv := s.core.chain.vY t j hj
  have hvac := hch.vac.1 j hj
  have hw := hch.weil
  obtain ⟨hX1, hX2⟩ := lsp_heq (colY_lt R.toLevCh (j.2 : (j : ℕ) < D.R.m))
  obtain ⟨hY1, hY2⟩ := lsp_heq (colY_lt R.toLevCh hj)
  have hv' : IsStepVecOf R.ψ R.θ (columnBlock R.toLevCh j).sp (columnBlock R.toLevCh (j + 1)).sp (ch.W.cart (.grid 0 j))
      (ch.W.cart (.grid 0 (j + 1))) (columnBlock R.toLevCh j).lat (columnBlock R.toLevCh (j + 1)).lat (colFrame R.toLevCh j)
      (colFrame R.toLevCh (j + 1)) (colDat R.toLevCh t j) (R.chi (j + 1)) (R.Q t) (R.xiR t) (ch.rm.vT 0 j) g :=
    stepVec_congr hX1.symm hY1.symm (hw.cartY j j.2).symm (hw.cartY (j + 1) hj).symm hX2.symm hY2.symm
      (colFrame_lt R.toLevCh j.2).symm (colFrame_lt R.toLevCh hj).symm
      (datY_heq (congrArg (fun V : HSp D => V.rank) hX1.symm) _ _ _ _ _ _ _ _ _ _ _) hvac.symm hg.symm hv
  obtain ⟨hf₀, e', he', hθ'⟩ := hv'
  have hsd := fun k (hk : k ≤ D.R.m) => (colY_isV D T R.toLevCh A.μ0 hL k hk).sd
  have hPg := GlobalTheory.LevelPlacesChosen.levelPlaces_subset_chosenPlaces ch.G hL
  have h1 := GlobalTheory.ExtDatTheta.isThetaAt_extDat (hsd j j.2.le) (hsd (j + 1) hj.le) hf₀ he he' ?_ hθ'
  swap
  · intro x hx
    unfold locPl
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union.2 (Or.inl (hPg h))
    · exact Finset.mem_union.2 (Or.inr h)
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ R.toLevCh.Pg ∪ R.toLevCh.Q t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have h3 := funext (GlobalTheory.ChainColRead.givenFn_eq_extDat ch.G ch.S.B hL hPg t j hj Φ e e' he he' hAA)
  refine ⟨?_, ?_⟩
  · rw [Units.val_one, one_smul]
    exact GlobalTheory.FlipStart.ColSB.isSBHalf_givenFn_down ch.G ch.S.B hL t j j.2 Φ e he
  · rw [Units.val_one, one_smul, h3, hw.ψ]
    exact h1

theorem innerStep : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  exact ⟨1, one_mem _, fun e he Φ => locVec_col s ch hch t j g hj hg e he Φ⟩

end GlobalTheory.ChainCol
