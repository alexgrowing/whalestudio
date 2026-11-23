import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeakApproxDVR
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak
import Formalism.PeriodIntegrals.WeakApproxDVR

open Formalism.MainNotions.G

theorem weakApprox_of_dvr (h : PI.WeakApproxDVR) {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw := by
  unfold PI.WeakApproxDVR at h
  unfold Formalism.L2.G.Cmp.WeakApprox
  have := hfr
  exact h E (Fin G.P.nV) G.P.W G.P.Qq iw p hp hpu hden hdist

theorem Formalism.L2.G.Cmp.weakApprox_of_approx_and_separation {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw :=
  weakApprox_of_dvr weak_approximation_dvr G iw hfr hp hpu hden hdist
