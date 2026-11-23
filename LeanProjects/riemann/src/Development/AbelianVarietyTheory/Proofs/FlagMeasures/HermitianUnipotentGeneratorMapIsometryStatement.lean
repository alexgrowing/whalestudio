import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  first | exact @GlobalTheory.RowStab.gen_isometry | exact GlobalTheory.RowStab.gen_isometry | (intros; apply GlobalTheory.RowStab.gen_isometry <;> assumption)
