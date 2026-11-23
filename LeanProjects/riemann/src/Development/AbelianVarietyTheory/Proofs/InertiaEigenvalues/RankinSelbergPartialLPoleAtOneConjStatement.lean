import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConj
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  first | (exact @GlobalTheory.RSPole.rs_pole_conj) | (exact GlobalTheory.RSPole.rs_pole_conj) | (intros; apply GlobalTheory.RSPole.rs_pole_conj  <;> assumption)
