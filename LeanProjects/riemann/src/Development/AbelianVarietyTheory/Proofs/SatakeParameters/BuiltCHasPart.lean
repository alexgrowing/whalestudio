import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

def Part.ofBuilt {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c) : Part w Z c.O where
  pin := b.pin
  col := b.col.toColT
  errX := b.errX
  tp := b.n.tp
  xi := b.n.xi
  qp := b.div.Qp
  ker0 := b.ker0
  ker_eq := b.ker_eq
  ker := b.ker

theorem builtC_hasPart : ∀ (𝒮 : Slots), (∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c) ∧
    ∀ K X f T c, IsBuilt 𝒮 K X f T c → positionOf HasPart K X f T c := fun 𝒮 =>
  have h : ∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c := fun _ _ _ _ _ _ _ ⟨b⟩ => ⟨Part.ofBuilt b⟩
  ⟨h, fun K X f T c hc => positionOf_mono h K X f T c hc⟩

end GlobalTheory.Svd

end
