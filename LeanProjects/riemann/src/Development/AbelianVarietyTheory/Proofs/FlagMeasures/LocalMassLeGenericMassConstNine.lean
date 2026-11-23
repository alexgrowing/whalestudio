import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds

namespace GlobalTheory

theorem localMass_le_genericMass_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ
  exact GlobalTheory.mass_pairingClass_bounds M hM H r k P hk hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl

end GlobalTheory
