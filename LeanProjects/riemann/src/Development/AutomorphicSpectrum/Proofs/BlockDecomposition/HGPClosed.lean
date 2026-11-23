import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.MirGP

theorem isClosed_HGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  intro k _ _ _ _ m j
  have h := GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (m + j + 1))
    (GlobalTheory.SmGL.Two (Fin m) (Fin (j + 1))) (GlobalTheory.BZMir.Leib.eGP m j)
  exact h.2.2.2.2.2.2.1.preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.MirGP
