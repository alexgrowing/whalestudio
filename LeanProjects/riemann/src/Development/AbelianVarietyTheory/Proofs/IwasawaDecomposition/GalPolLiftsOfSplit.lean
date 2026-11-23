import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GalAllPlaces

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial

theorem exists_rep_uniform (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (C : CGTrue hL D T)
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (ha : 1 ≤ a) (π : D.naut.CG a) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) :
    ∃ ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
        ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
          IsFrob (F := D.host.E) B (normV w) σ →
          ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
            galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
  have := host_isCMField D.host
  have hr' : (C.e a π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := exists_wdOf_eq_locPar hL hF hG D.nd.Om ι ha (C.e a π).1 ((C.csd a π).1 hc) hr'
  refine ⟨r, h1, fun w hl hu B σ hB hσ => ?_⟩
  have hu' := (D.naut.unr_tw _ ((1 - (a : ℝ)) / 2)).2 hu
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    rw [T.tw, C.loc, h3]
    rfl
  rw [galPol, T.frobEig w _ hu', e]
  exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hσ

end GlobalTheory.GalAllPlaces

end

noncomputable section

namespace GlobalTheory.GalAllPlaces

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem galPol_lifts_of_split : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.CGTrue hL D T → ∀ (K : Type) [Field K] (e : K →+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e := by
  intro hL hF hG hCh D T C K _ e π hc hr hsplit
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] :=
    fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP
  have hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w) :=
    (eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)
  obtain ⟨ρ, hρc, hρ⟩ := exists_rep_uniform hL hF hG C 2 ι ha π hc hr
  letI : Algebra K ℂ := e.toAlgebra
  have key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) →
      (P w).map (γ : ℂ →+* ℂ) = P w := by
    intro γ
    obtain ⟨ρ', hρ'c, hρ'⟩ := exists_rep_uniform hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr
    have hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w :=
      hsplit.mono fun w hw hs => by
        obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 (hw hs)
        simp only [hP]
        rw [← hq, Polynomial.map_map]
        congr 1
        ext x
        exact γ.commutes x
    have hall := hU.and hfix
    rw [Filter.eventually_cofinite] at hall
    set S := hall.toFinset with hS
    have hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map
        (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ)) := by
      intro g
      rw [Polynomial.map_map]
      rfl
    have heq := GlobalTheory.charpoly_eq_of_eqOn_dense
      (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)))
      (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _
      (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by
        rintro g ⟨w, hwS, hsp, B, hB, hFr⟩
        have hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧
            (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w) := by
          by_contra h
          exact hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)
        apply Polynomial.map_injective ι.toRingHom ι.injective
        rw [hρ w hw.1.1 hw.1.2 B g hB hFr]
        apply Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective
        rw [← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])
    intro w hw
    obtain ⟨σ, hσ⟩ := exists_isFrob (D.nd.plOm.2 w)
    have h1 := hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    have h2 := hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    rw [hmap, ← heq σ, h1] at h2
    exact h2
  filter_upwards [hU] with w hw
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)
    simpa [Polynomial.coeff_map] using this

end GlobalTheory.GalAllPlaces

end
