import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanContragredient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.ThetaPf

open GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.ThetaW

theorem thetaProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.ThetaProd k := by
  intro r t V W _ _ _ _ A B _ _
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum (rfl : r + t = r + t)) (stdSum (add_comm t r))
    (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap (k := k) A B
  exact ⟨(compInvTEquiv (prod₂ A B)).symm.trans (κ.symm.trans
    (ind₂Equiv _ (τ.trans (extTensorCongr (compInvTEquiv B) (compInvTEquiv A)))))⟩

end PositivityTheory.RgUd.Exp.ThetaPf

end
