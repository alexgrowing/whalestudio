import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueEffectiveCartierStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGlueCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTwistedCoverStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem exists_mem_range_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F}
    {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i))
    (u : ∀ i, (C i).X ⟶ Z.X) (hC : IsCover (algebraMap (𝓞 c.F) c.F) R a b ω)
    (hu : ∀ i, IsChartOf Z (C i) (a i) (b i) (u i)) : ∀ x : Z.X, ∃ i, x ∈ Set.range (u i) := by
  intro x
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range a) ≤ (Z.s x).asIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    by_contra hi
    apply h i
    rw [(hu i).2.2.1]
    exact hi
  rw [hC.2.2] at hle
  exact (Z.s x).isPrime.ne_top (top_le_iff.1 hle)

theorem isPol_of_charts : PolMapSt → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)]
    {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i} {ω : ∀ i, R i →+* c.F} (Z : GMod Xo c) (C : ∀ i, Model Xo c (ω i))
    (u : ∀ i, (C i).X ⟶ Z.X) (φ : InvFun (𝓞 E)) (m : ℕ) (BD : ∀ i, EffCartierData (C i).X), IsTwInv H φ →
    IsCover (algebraMap (𝓞 c.F) c.F) R a b ω → (∀ i, IsChartOf Z (C i) (a i) (b i) (u i)) →
    (∀ i, IsPol φ m (C i) (BD i)) → ∃ BD' : EffCartierData Z.X, IsPol φ m Z BD' := by
  intro hPM E _ _ _ H D l Xo c I _ R _ a b ω Z C u φ m BD htw hC hu hP
  have hcov := exists_mem_range_chart Z C u hC hu
  have hoi : ∀ i, IsOpenImmersion (u i) := fun i => (hu i).1
  obtain ⟨DZ, hD⟩ := GlobalTheory.T.glue_effective_cartier u BD hoi hcov (GlobalTheory.T.polarization_twisted_cover hPM Z C u φ m BD htw hC hu hP)
  refine ⟨DZ, GlobalTheory.T.polarization_glue_cover Z C u φ DZ BD hoi (fun i => (hu i).2.2.2.1) (fun i => (hu i).2.2.2.2) hcov hD
    (fun i => (hP i).1), ?_⟩
  have hpr : IsProper Z.s := projProper _ _ _ Z.proj
  have hc : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have hq : QuasiSeparatedSpace Z.X := quasiSeparatedSpace_of_quasiSeparated Z.s
  exact GlobalTheory.T.ample_of_local_affine_cover Z.s u a (polOf Z m DZ) hc hq hC.2.2 hoi (fun i => (hu i).2.2.1)
    (fun i => (GlobalTheory.T.polarization_open_immersion Z (C i) (u i) DZ (BD i) m (hoi i) (hu i).2.2.2.2 (hD i)).1 (hP i).2)

end GlobalTheory.TorRef
