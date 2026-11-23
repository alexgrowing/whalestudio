import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  first | exact @GlobalTheory.CubeDual.abelianDeRham_duality | exact GlobalTheory.CubeDual.abelianDeRham_duality | (intros; apply GlobalTheory.CubeDual.abelianDeRham_duality <;> assumption)
