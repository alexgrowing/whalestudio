import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem giso_tw_prod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ) : GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) :=
  ⟨(GlobalTheory.LocGL.multiProdTwistEquiv (two (stdSum rfl)) (twoRep A.ρ B.ρ)
      (GlobalTheory.LocGL.isSmoothChar_absPow (k := k) (s : ℂ))).trans
    (GlobalTheory.LocGL.multiProdEquiv _ fun x => match x with
      | false => Representation.Equiv.refl _
      | true => Representation.Equiv.refl _)⟩

end GlobalTheory.CompanionTheory.LeibOrd

end
