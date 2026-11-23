import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitInt

theorem intAt_iff_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (ha : a ∈ GlobalTheory.FinPl.idAt D (· = q.v)) :
    (a ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
  have he := GlobalTheory.UpMem.finPart_e_int q
  rw [q.int_iff, q.int_iff, q.sec_pr, q.sec_pr, map_mul, map_mul]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨GlobalTheory.FinPl.FrameLat.mul_mem_intAE he h,
      GlobalTheory.FinPl.FrameLat.mul_mem_intAE he (GlobalTheory.IdemSupport.finPart_cA_mem h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨ha, ?_⟩
    have hsum : a = q.e * a + cA D (q.e * cA D a) := by
      rw [map_mul, Formalism.L2.Theta.cA_cA, ← add_mul]
      exact ((GlobalTheory.FinPl.FrameLat.idem_iff q a).1 ha).symm
    have h3 : finPart D (cA D (q.e * cA D a)) ∈ intAE D := by
      apply GlobalTheory.IdemSupport.finPart_cA_mem
      rw [map_mul]; exact h2
    rw [hsum, (finPart D).map_add, (finPart D).map_mul]
    exact add_mem h1 h3

end GlobalTheory.SplitInt
end
