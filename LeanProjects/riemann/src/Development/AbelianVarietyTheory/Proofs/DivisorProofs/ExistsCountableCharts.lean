import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.CountableCharts

theorem isHolTo_finChart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (c : GlobalTheory.AlgChart p σ D) : IsHolTo c.finChart.target fun z => (c.finChart.symm z).1 := by
  have h1 := GlobalTheory.LocLift.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c) c.finChart.open_target
    (β := fun z => (EuclideanSpace.equiv (Fin D) ℂ).symm z)
    (EuclideanSpace.equiv (Fin D) ℂ).symm.differentiable.differentiableOn fun z hz => hz
  refine GlobalTheory.LocLift.isHolTo_congr h1 fun v _ => ?_
  simp [GlobalTheory.AlgChart.finChart_symm_apply]

theorem exists_countable_charts : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → ∀ (Q : Set (Fin d → ℂ) → ((Fin d → ℂ) → (Sp ℂ ⟶ X)) → Prop), (∀ B y b₀, IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∃ B', IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ Q B' y) → ∃ (K : Type) (_ : Countable K) (B : K → Set (Fin d → ℂ)) (y : K → (Fin d → ℂ) → (Sp ℂ ⟶ X)), (∀ i, IsOpen (B i) ∧ (∀ b ∈ B i, y i b ≫ s = spMap (RingHom.id ℂ)) ∧ IsHolTo (B i) (y i) ∧ Set.InjOn (y i) (B i) ∧ Q (B i) (y i)) ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap (RingHom.id ℂ) → ∃ i, x ∈ y i '' B i := by
  intro X s d hs hq Q hQ
  haveI := hs
  haveI := hq
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hc : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ c : GlobalTheory.AlgChart s (RingHom.id ℂ) d, x ∈ c.e.source :=
    fun x => GlobalTheory.AlgChart.exists_mem_source x
  choose c hc using hc
  have hB : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ B', IsOpen B' ∧ (c x).finChart x ∈ B' ∧
      B' ⊆ (c x).finChart.target ∧ Q B' (fun z => ((c x).finChart.symm z).1) := fun x =>
    hQ _ _ _ (c x).finChart.open_target ((c x).finChart.map_source (hc x))
      (fun b _ => ((c x).finChart.symm b).2) (isHolTo_finChart_symm (c x))
  choose B' hB'o hB'm hB'sub hB'Q using hB
  have hN : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ),
      (c x).finChart.source ∩ (c x).finChart ⁻¹' B' x ∈ 𝓝 x := fun x =>
    ((c x).finChart.isOpen_inter_preimage (hB'o x)).mem_nhds ⟨hc x, hB'm x⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.countable_cover_nhds hN
  refine ⟨T, hTc.to_subtype, fun i => B' i, fun i z => ((c i).finChart.symm z).1, fun i =>
    ⟨hB'o i, fun b _ => ((c i).finChart.symm b).2,
      GlobalTheory.LocLift.isHolTo_mono (isHolTo_finChart_symm (c i)) (hB'o i) (hB'sub i), ?_, hB'Q i⟩, ?_⟩
  · intro a ha b hb hab
    exact (c i).finChart.symm.injOn (by simpa using hB'sub i ha) (by simpa using hB'sub i hb)
      (Subtype.ext hab)
  · intro x hx
    have hmem : (⟨x, hx⟩ : GlobalTheory.CxPts s (RingHom.id ℂ)) ∈ ⋃ t ∈ T,
        (c t).finChart.source ∩ (c t).finChart ⁻¹' B' t := hTU ▸ Set.mem_univ _
    obtain ⟨t, ht, hm⟩ := Set.mem_iUnion₂.1 hmem
    exact ⟨⟨t, ht⟩, (c t).finChart ⟨x, hx⟩, hm.2, by
      show ((c t).finChart.symm ((c t).finChart ⟨x, hx⟩)).1 = x
      rw [(c t).finChart.left_inv hm.1]⟩

end GlobalTheory.CountableCharts
