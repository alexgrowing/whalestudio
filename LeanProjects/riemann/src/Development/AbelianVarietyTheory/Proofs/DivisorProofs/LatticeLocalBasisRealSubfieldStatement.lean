import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLocalBasisRealSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_local_basis_real_subfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : GL (Fin r) E), (∀ j, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ (algebraMap (maximalRealSubfield E) E s • fun i => (P : Matrix (Fin r) (Fin r) E) i j) ∈ Λ) → (∀ x ∈ Λ, ∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ algebraMap (maximalRealSubfield E) E s • ((P⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ GlobalTheory.AdelicU.stdLattice E r) → ∀ (i j : Fin r), (∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s * (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ * (P : Matrix (Fin r) (Fin r) E)) i j)) ∧ (∃ s : 𝓞 (maximalRealSubfield E), s ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap (maximalRealSubfield E) E s * (Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (P : Matrix (Fin r) (Fin r) E) * Gᵀ * (P : Matrix (Fin r) (Fin r) E))⁻¹ i j)) := by
  first | exact @GlobalTheory.FrameDual.gram_integral_at | exact GlobalTheory.FrameDual.gram_integral_at | (intros; apply GlobalTheory.FrameDual.gram_integral_at <;> assumption)
