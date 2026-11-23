import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noetherian_sh_factorization : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A → ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧ ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  first | (exact @GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (exact GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor) | (intros; apply GlobalTheory.NoethSHFactor.exists_noetherian_sh_factor  <;> assumption)
