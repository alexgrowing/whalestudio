import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackOfSurjectiveToPushforwardStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionPullback_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
