import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapCompNeg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by
  first | exact @GlobalTheory.RowStab.gen_comp_gen_neg | exact GlobalTheory.RowStab.gen_comp_gen_neg | (intros; apply GlobalTheory.RowStab.gen_comp_gen_neg <;> assumption)
