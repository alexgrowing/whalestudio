import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
open Matrix GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UAut

theorem isRealLine_oneP (D : D7) (θ : InfF D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : X ∈ lieAt V τ) :
    GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  obtain ⟨-, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hZ : Xᴴ * V.gram.map (embOverOf D τ).1 + V.gram.map (embOverOf D τ).1 * X = 0 := hX
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine (isCMExt_host D) (h2 V) (embOverOf D τ) hZ
  refine ⟨placeOf D τ, embOverOf D τ, X, hZ, fun t => ⟨_, ?_, hγ t⟩⟩
  rw [oneP, ← hγ t, GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), atTau_archEquiv hθ V _ rfl]

end GlobalTheory.UAut
