import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood

namespace PositivityTheory.RgUd.TP.Desc.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem desc_of (hR : Restr k) (hP : PieceGood k) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : Desc k := by
  refine ⟨fun n Z => mu Z, fun n Z hZ χ => ?_⟩
  obtain ⟨N, q, Z', hZ', hmu, hq, hr, hb, hpull⟩ := hR p n Z hZ
  obtain ⟨l, hl⟩ := hpull χ
  obtain ⟨m, F, hF, hg⟩ := hl fun χ' _ => hP p hU N q Z' hZ' hq hr hb χ'
  refine ⟨m, F, hF, fun i => (hg i).imp_right fun ⟨N', S, hS, hlt, hv⟩ ih => hv (ih N' S hS hlt)⟩

end PositivityTheory.RgUd.TP.Desc.Asm
