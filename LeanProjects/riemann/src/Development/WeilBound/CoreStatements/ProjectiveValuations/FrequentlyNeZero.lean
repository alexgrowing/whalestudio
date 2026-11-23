import Development.WeilBound.CoreStatements.ProjectiveValuations.DifferentiableAtOfLines
import Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsFrBorOfMatches
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicArcSmoothAlgebraNonvanishing
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

theorem frequently_ne_zero {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [Smooth p] {σ : F →+* ℂ} {W : Y.Opens}
    (hW : IsAffineOpen W) [IsDomain Γ(Y, W)] {g : Γ(Y, W)} (hg : g ≠ 0) {y : GlobalTheory.CxPts p σ} (hy : y ∈ ptsIn p σ W)
    {N : Set (GlobalTheory.CxPts p σ)} (hN : N ∈ 𝓝 y) : ∃ y' ∈ N, ev p σ W g y' ≠ 0 := by
  classical
  letI : Algebra F Γ(Y, W) := (algX p W).toAlgebra
  have hs : (algX p W).Smooth :=
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top)
  obtain ⟨ψ, ρ, hψ, h0, hσ, hne⟩ := GlobalTheory.HolArc.exists_holPts_ne_zero F Γ(Y, W) hs (evHom hy) g hg
  have ha : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ a, ψ u (algX p W a) = σ a := fun u hu a =>
    (RingHom.congr_fun (hσ u hu) a).trans ((ev_eq hy _).symm.trans (ev_algX hy a))
  let e : ℂ → GlobalTheory.CxPts p σ := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then ofHom hW (ψ u) (ha u hu) else y
  have hb := Metric.ball_mem_nhds (0 : ℂ) hψ.1
  have hev : ∀ u ∈ Metric.ball (0 : ℂ) ρ, e u ∈ ptsIn p σ W ∧ ∀ f, ev p σ W f (e u) = ψ u f := fun u hu => by
    simp only [e, dif_pos hu]
    exact ⟨ofHom_mem _ _ _, ev_ofHom _ _ _⟩
  have ht : Tendsto e (𝓝 0) (𝓝 y) := by
    refine tendsto_subtype_rng.2 (GlobalTheory.Points.tendsto_of_isAffineOpen hW hy
      (eventually_of_mem hb fun u hu => (hev u hu).1) fun f => ?_)
    have h₁ := ((hψ.2 f).differentiableAt hb).continuousAt.tendsto
    rw [h0, ← ev_eq hy] at h₁
    exact h₁.congr' (eventually_of_mem hb fun u hu => ((hev u hu).2 f).symm)
  obtain ⟨u, ⟨h₁, h₂⟩, h₃⟩ := (((ht.eventually hN).and hb).filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))
    |>.and eventually_mem_nhdsWithin).exists
  exact ⟨e u, h₁, by rw [(hev u h₂).2]; exact hne u h₂ h₃⟩

theorem mem_open_of_ptY (T : TorFlag Xo c) (x : FrPt Xo c (CAt σ)) (y : GlobalTheory.CxPts (flagStr T.X) σ)
    (e : T.X.ptY x = zOf y) : y ∈ ptsIn _ σ (flagOpen T.X) := by
  have : ⊤ ≤ T.X.ptY x ⁻¹ᵁ flagOpen T.X := by
    rw [← T.X.pt_inc]
    exact GlobalTheory.FlagMod.le_preimage_map T.X.inc (top_le_inc T.X) le_top
  rw [e] at this
  exact this

end DifferentiableLines
