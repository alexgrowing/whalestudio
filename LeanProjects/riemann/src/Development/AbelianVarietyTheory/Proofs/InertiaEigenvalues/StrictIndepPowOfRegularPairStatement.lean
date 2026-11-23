import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictIndepPowOfRegularPair
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_indep_pow_of_regular_pair : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (p q : S) (ι : Type) (b : ι → A), (∀ x : A, s p * x = 0 → x = 0) → (∀ x : A, s p ∣ s q * x → s p ∣ x) → (∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s → ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) → ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ ((Ideal.span {p} ⊔ Ideal.span {q}) ^ m).map s → ∀ i, a i ∈ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n := by
  first | exact @GlobalTheory.BSP.strict_indep_pow | exact GlobalTheory.BSP.strict_indep_pow | (intros; apply GlobalTheory.BSP.strict_indep_pow <;> assumption)
