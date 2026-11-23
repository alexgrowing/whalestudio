import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverChartsHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightPrimeSumStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
open GlobalTheory.EqHalf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqHalf

theorem eqData_geo : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ c : O.s.Comp,
    ∃ (bar : 𝓞 D.host.E ≃+* 𝓞 D.host.E) (Φ : Set (D.host.E →+* D.what₂.LL))
      (β : Fin (D.R.f * O.N) → (D.host.E →+* D.what₂.LL))
      (ρ : 𝓞 D.host.E →+* Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ)
      (J : Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ),
      (∀ σ τ : D.host.E →+* D.what₂.LL, (∀ α : 𝓞 D.host.E, τ (α : D.host.E) = σ ((bar α : 𝓞 D.host.E) : D.host.E)) →
        (σ ∈ Φ ↔ τ ∉ Φ)) ∧ IsUnit J.det ∧ (∀ α, (ρ α).transpose * J = J * ρ (bar α)) ∧
      ∀ k : ℕ, EqData
        (fun i : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
          (wholeSym (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))))
        (fun i : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
          (eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))))
        β (fun τ => if τ ∈ Φ then vDiff D.host.E p else 0) ρ J p k := by
  intro h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c
  obtain ⟨b⟩ := nonempty_basis O
  refine ⟨O.A.H.bar, cmSet O, fun l => letterEmb O l, chiAct O.S.Dw b, dualForm O.S.Dw b,
    fun σ τ h => mem_cmSet_iff O σ τ h, isUnit_det_dualForm O.S.Dw b, chiAct_adj O.S.Dw b, fun k => ?_⟩
  obtain ⟨V, W, Ch, U, H, T', hW, hcov, hT, hL, hL', hreg, hpt⟩ :=
    GlobalTheory.T.exists_cover_charts_height h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega)
  refine ⟨V, W, Ch, U, H, dgOf O c, T', hW, hcov, hT, hL, hL', fun a => ⟨hreg a, ?_, ?_⟩, ?_, ?_⟩
  · intro v hv e y hy z yt hz hyt ha
    have hpv : (resP v).Prime := hv ▸ hp
    exact GlobalTheory.T.local_height_prime_bound h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega) v hpv e y Ch _ _ hv
      (hpt v hv e y hy z yt hz hyt hpv) a ha
  · intro v hv e y hy z yt hz hyt ha
    have hpv : (resP v).Prime := hv ▸ hp
    exact GlobalTheory.T.local_height_prime_comparison h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega) v hpv e y Ch _ _ hv
      (hpt v hv e y hy z yt hz hyt hpv) a ha
  · intro v hv e y hy z yt hz hyt a ha
    have hpv : (resP v).Prime := hv ▸ hp
    have hP := hpt v hv e y hy z yt hz hyt hpv
    exact ⟨GlobalTheory.T.local_height_prime_vanishing h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega) v hpv e y Ch _ _ hv hP k (by omega) a ha,
      fun a' ha' => GlobalTheory.T.local_height_prime_integrality h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega) v hpv e y Ch _ _ hv hP k
        (by omega) a a' ha ha'⟩
  · intro v hv e y hy z yt hz hyt a ha
    have hpv : (resP v).Prime := hv ▸ hp
    exact GlobalTheory.T.local_height_prime_sum h1 h2 h3 h4 h5 D O hO T R hR p hp hpT c b (k + 3) (by omega) v hpv e y Ch _ _ hv
      (hpt v hv e y hy z yt hz hyt hpv) k (by omega) a ha

end GlobalTheory.EqHalf

end
