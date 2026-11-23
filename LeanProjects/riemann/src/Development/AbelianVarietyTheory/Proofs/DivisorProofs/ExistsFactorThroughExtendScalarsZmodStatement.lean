import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughExtendScalarsZmod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_extendScalars_zmod : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K), ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) := by
  first | exact @GlobalTheory.EtC.SemiMap.factor_extCx | exact GlobalTheory.EtC.SemiMap.factor_extCx | (intros; apply GlobalTheory.EtC.SemiMap.factor_extCx <;> assumption)
