import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PrimIdemZ

namespace PositivityTheory.RgUd.TP.Desc.Restr.Pphi1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiE

theorem phiEx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k → PhiEx k := by
  intro hF p c _ _ n Z hZ hn
  obtain ⟨d, -, ⟨B⟩⟩ := fb_exists hF p c
  exact ⟨n * d, Z' B Z, φ B, e B,
    { inj := φ_inj B
      emb := φ_emb B
      econt := continuous_eF B
      econt' := continuous_eI B
      intertw := fun x v => key B x v
      carrier := coe_Z' B Z
      cen := cen B Z
      gz := gz B Z
      scal := φ_scal B
      cr := cr B Z hZ
      mu := mu_Z' B Z
      roots := roots B Z
      nil := nil B Z hn }⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Pphi1
