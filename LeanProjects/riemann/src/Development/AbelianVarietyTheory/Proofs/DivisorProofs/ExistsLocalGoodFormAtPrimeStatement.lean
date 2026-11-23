import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGoodFormAtPrime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_good_form_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (π : 𝓞 (maximalRealSubfield E)), π ∈ v.asIdeal → π ∉ v.asIdeal ^ 2 → ∃ P : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), GoodForm (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (P : Matrix (Fin r) (Fin r) _) * JR (Fv (maximalRealSubfield E) v) Gᵀ * (P : Matrix (Fin r) (Fin r) _)) ∧ ∀ k : ℕ, GlobalTheory.TamCnt.locCong (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k = (congSU (intA (E := E) v) (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) (IsCMField.complexConj E).toAlgHom) (P : Matrix (Fin r) (Fin r) _) * JR (Fv (maximalRealSubfield E) v) Gᵀ * (P : Matrix (Fin r) (Fin r) _)) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ[maximalRealSubfield E] algebraMap (maximalRealSubfield E) E (π : maximalRealSubfield E)) k).map (MulAut.conj P).toMonoidHom := by
  first | exact @GlobalTheory.SUFrame.frame_conj | exact GlobalTheory.SUFrame.frame_conj | (intros; apply GlobalTheory.SUFrame.frame_conj <;> assumption)
