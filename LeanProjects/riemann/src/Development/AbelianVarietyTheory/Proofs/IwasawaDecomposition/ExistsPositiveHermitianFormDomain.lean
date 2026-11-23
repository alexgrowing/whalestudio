import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BetaLowerAndSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivApplyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDerivativeInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPullbackToFrameDomainStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

namespace GlobalTheory.KaePull

open GlobalTheory.HessForm

theorem kae_pull : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s), ∃ a : Pt D.what₂.Tau j (N - j) → Pt D.what₂.Tau j (N - j) →ₗ[ℂ] Pt D.what₂.Tau j (N - j) →ₗ⋆[ℂ] ℂ, (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a z ζ ξ = starRingEnd ℂ (a z ξ ζ)) ∧ (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ, ξ ≠ 0 → 0 < (a z ξ ξ).re) ∧ (∀ ξ ζ, HodgeDomain.SmoothOn fun z => a z ξ ζ) ∧ ∀ W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → ∀ ξ, (a z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ := by
  intro D A N j S κ s L k x
  classical
  have hK := x.kae_kaehler κ.σ₀

  have key : ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ W' φ', IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W' φ' →
      s.toCpt L k z ∈ W' → ContDiffAt ℝ 2 (fun v => φ' (s.toCpt L k (unflat v))) (flat z) ∧
        ∀ c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim, s.toCpt L k z ∈ c.e.source → ∀ ξ,
          ddc (φ' ∘ s.toCpt L k) z ξ = x.kae κ.σ₀ c (s.toCpt L k z)
            (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ)).ofLp := by
    intro z hz W' φ' hp hW
    obtain ⟨ho, hs, hd⟩ := GlobalTheory.T.smooth_pullback_to_frame_domain D A N j S κ s L k W' φ' hp.1 hp.2.1
    have hzf : flat z ∈ DomFlat D.what₂.Tau j (N - j) := hz
    have hm : flat z ∈ {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W'} := Set.mem_sep hzf hW
    have hc2 : ContDiffAt ℝ ∞ (fun v => φ' (s.toCpt L k (unflat v))) (flat z) := hs.contDiffAt (ho.mem_nhds hm)
    refine ⟨hc2.of_le (WithTop.coe_le_coe.2 le_top), fun c hc ξ => ?_⟩
    rw [hd c z hz hW hc ξ, hp.2.2 c _ hc hW]
  have indep : ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ W₁ φ₁ W₂ φ₂,
      IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W₁ φ₁ → s.toCpt L k z ∈ W₁ →
      IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W₂ φ₂ → s.toCpt L k z ∈ W₂ →
      ∀ ξ, ddc (φ₁ ∘ s.toCpt L k) z ξ = ddc (φ₂ ∘ s.toCpt L k) z ξ := by
    intro z hz W₁ φ₁ W₂ φ₂ h₁ hW₁ h₂ hW₂ ξ
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (s.toCpt L k z) (D := S.Dw.dim)
    rw [(key z hz W₁ φ₁ h₁ hW₁).2 c hc ξ, (key z hz W₂ φ₂ h₂ hW₂).2 c hc ξ]
  choose W φ hmem hpot using fun z : Pt D.what₂.Tau j (N - j) => hK.1 (s.toCpt L k z)
  have dsq : ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ W' φ', IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W' φ' →
      s.toCpt L k z ∈ W' → ∀ ξ,
        (sesq (hess (fun v => φ' (s.toCpt L k (unflat v))) (flat z)) ξ ξ).re = ddc (φ' ∘ s.toCpt L k) z ξ :=
    fun z hz W' φ' hp hW ξ => (ddc_eq_sesq (f := φ' ∘ s.toCpt L k) (key z hz W' φ' hp hW).1 ξ).symm
  have herm : ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ W' φ', IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W' φ' →
      s.toCpt L k z ∈ W' → ∀ ξ ζ, sesq (hess (fun v => φ' (s.toCpt L k (unflat v))) (flat z)) ζ ξ =
        starRingEnd ℂ (sesq (hess (fun v => φ' (s.toCpt L k (unflat v))) (flat z)) ξ ζ) :=
    fun z hz W' φ' hp hW => sesq_herm (hess_symm (key z hz W' φ' hp hW).1)
  refine ⟨fun z => sesq (hess (fun v => φ z (s.toCpt L k (unflat v))) (flat z)), fun z hz =>
    herm z hz _ _ (hpot z) (hmem z), fun z hz ξ hξ => ?_, fun ξ ζ => ?_, fun W' φ' hp z hz hW ξ => ?_⟩
  · rw [dsq z hz _ _ (hpot z) (hmem z)]
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (s.toCpt L k z) (D := S.Dw.dim)
    rw [(key z hz _ _ (hpot z) (hmem z)).2 c hc ξ]
    refine hK.2 c _ hc _ fun h0 => hξ ?_
    have hinj := GlobalTheory.T.chart_derivative_injective D A N j S κ s L k c z hz hc
    have h1 : fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ) = 0 := by
      have := congrArg (WithLp.toLp 2) h0
      simpa using this
    have h2 : flat ξ = 0 := hinj (h1.trans (map_zero _).symm)
    funext τ a b
    exact congrFun h2 (τ, a, b)
  · refine contDiffOn_of_locally_contDiffOn fun v0 hv0 => ?_
    obtain ⟨ho, hs, -⟩ := GlobalTheory.T.smooth_pullback_to_frame_domain D A N j S κ s L k (W (unflat v0)) (φ (unflat v0)) (hpot (unflat v0)).1
      (hpot (unflat v0)).2.1
    have hm : v0 ∈ {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W (unflat v0)} := Set.mem_sep hv0 (hmem _)
    refine ⟨_, ho, hm, ((contDiffOn_sesq hs ho ξ ζ).mono Set.inter_subset_right).congr ?_⟩
    rintro v ⟨hv, hvW⟩
    have hz : unflat v ∈ DomI D.what₂.Tau j (N - j) := hv
    have e := ext_of_re (herm (unflat v) hz _ _ (hpot (unflat v)) (hmem _))
      (herm (unflat v) hz _ _ (hpot (unflat v0)) hvW.2) fun η => by
        rw [dsq _ hz _ _ (hpot _) (hmem _), dsq _ hz _ _ (hpot _) hvW.2,
          indep _ hz _ _ _ _ (hpot _) (hmem _) (hpot _) hvW.2]
    exact congrArg (fun b => b ξ ζ) e
  · rw [dsq z hz _ _ (hpot z) (hmem z), indep z hz _ _ _ _ (hpot z) (hmem z) hp hW]

end GlobalTheory.KaePull
