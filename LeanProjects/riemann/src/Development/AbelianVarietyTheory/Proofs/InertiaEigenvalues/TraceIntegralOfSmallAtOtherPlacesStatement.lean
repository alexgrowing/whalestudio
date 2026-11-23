import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlaces
import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integral_of_small_at_other_places : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  first | exact @GlobalTheory.TraceSmall.trace_le_one | exact GlobalTheory.TraceSmall.trace_le_one | (intros; apply GlobalTheory.TraceSmall.trace_le_one <;> assumption)
