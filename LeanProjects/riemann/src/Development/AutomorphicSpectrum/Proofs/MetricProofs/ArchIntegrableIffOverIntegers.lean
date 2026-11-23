import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheetsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem chernIntegrableOn_and_chernInt_congr {k : Type} [CommRing k] {Y : Scheme} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} (φ : GlobalTheory.Weight q σ B) (d : ℕ) {S : Set (GlobalTheory.CxPts q σ)}
    (hS : MeasurableSet S) {f g : GlobalTheory.CxPts q σ → ℝ} (h : Set.EqOn f g S) :
    (φ.ChernIntegrableOn d S f ↔ φ.ChernIntegrableOn d S g) ∧ φ.chernInt d S f = φ.chernInt d S g := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.Weight.ChernIntegrableOn
    rw [integrableOn_congr_fun h hS, integrableOn_congr_fun h hS]
  · unfold GlobalTheory.Weight.chernInt
    rw [setIntegral_congr_fun hS h, setIntegral_congr_fun hS h]

theorem archInt_over_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (ψ : Weight t τ N.B) (ν : Weight t τ M.B), WOver N.φ ψ → WOver M.φ ν → ψ.IsCInf → ∀ (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → ψ.chernInt e (offSupp t τ (M.div hr)) (logNorm ν r) = N.archInt M e hr) := by
  intro k _ X _ p t τ D hX N M ψ ν hψN hνM hψ e r hr
  by_cases hσ : Nonempty (k →+* ℂ)
  · obtain ⟨σ₀⟩ := hσ
    haveI : CharZero k := σ₀.charZero
    haveI := hX.isDomain
    haveI := hX.finite
    have hS : MeasurableSet (offSupp t τ (M.div hr)) := (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    obtain ⟨h1, h2⟩ := GlobalTheory.T.chernIntegrableOn_iff_sheets k X p t τ hX.isProjOver e N.B N.φ ψ hψN N.cInf hψ _ hS (logNorm ν r)
    have hmeas : ∀ σ : k →+* ℂ, MeasurableSet (offSupp p σ (M.div hr)) :=
      fun σ => (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    have hEq : ∀ σ : k →+* ℂ, Set.EqOn (fun z => logNorm ν r (GlobalTheory.CompanionTheory.Ar.BaseZ.sheet t τ z))
        (logNorm (M.φ σ) r) (offSupp p σ (M.div hr)) :=
      fun σ y hy => GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hνM r hr σ y hy
    have hiff : ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr := by
      rw [h1]
      unfold GlobalTheory.HermLB.ArchIntegrable
      exact forall_congr' fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).1
    refine ⟨hiff, fun hInt => ?_⟩
    rw [h2 (hiff.mpr hInt)]
    unfold GlobalTheory.HermLB.archInt
    exact finsum_congr fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).2
  · have hE : IsEmpty (k →+* ℂ) := not_nonempty_iff.mp hσ
    haveI : IsEmpty (GlobalTheory.CxPts t τ) := ⟨fun y => hE.false (Spec.preimage (Subtype.val y ≫ p)).hom⟩
    have hS0 : offSupp t τ (M.div hr) = ∅ := Set.eq_empty_of_isEmpty _
    have hA : N.ArchIntegrable M e hr := by
      unfold GlobalTheory.HermLB.ArchIntegrable
      intro σ
      exact hE.elim σ
    refine ⟨⟨fun _ => hA, fun _ => ?_⟩, fun _ => ?_⟩
    · unfold GlobalTheory.Weight.ChernIntegrableOn
      rw [hS0]
      exact ⟨integrableOn_empty, integrableOn_empty⟩
    · unfold GlobalTheory.HermLB.archInt GlobalTheory.Weight.chernInt
      rw [hS0, finsum_of_isEmpty]
      simp

end GlobalTheory.CompanionTheory.Ar.BaseZ
