import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

namespace GlobalTheory.TorRef

theorem blowProjSt : BlowProjSt := fun _ _ _ _ s J hs =>
  let ⟨X', π, hb, hp, _⟩ := GlobalTheory.ProjBlowup.exists_blowup s hs J
  ⟨X', π, hb, hp⟩

end GlobalTheory.TorRef
