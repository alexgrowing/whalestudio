import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartOfOpenImmersionImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartOfOpenImmersionPreimageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationPullIsLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationComapOpenImmersionStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

namespace GlobalTheory.PolOpen

theorem isAmpleLB_polOf_iff_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (v : Y'.X ⟶ Y.X) (DY : EffCartierData Y.X) (DY' : EffCartierData Y'.X) (m : ℕ), IsOpenImmersion v → Nonempty (SABMap Y'.t Y.t v) → DY.idealSheaf.comap v = DY'.idealSheaf → (GlobalTheory.IsAmpleLB (polOf Y' m DY') ↔ GlobalTheory.IsAmpleLB ((polOf Y m DY).pull v)) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' v DY DY' m hv hm hI
  have covY' : (detLie Y').IsLB ↔ ∀ y, ∃ M' : MChart Y', y ∈ M'.U :=
    ⟨fun h y => TopologicalSpace.Opens.mem_iSup.1 (h.cover.ge (Set.mem_univ y)),
      fun h => isLB_of_ev _ (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (h x))
        fun i j k _ _ z => ev_detChg_mul i j k z⟩
  have lbY' : (polOf Y' m DY').IsLB ↔ ∀ y, ∃ M' : MChart Y', y ∈ M'.U :=
    ⟨fun h => covY'.1 (PolFin.isLB_detLie_of_polOf h), fun h =>
      CechPic.isLB_tens (isLB_lbPow (CechPic.isLB_dual (covY'.2 h)) m) (CechPic.isLB_dual DY'.isLB_lb)⟩
  have lbY : ((polOf Y m DY).pull v).IsLB ↔ ∀ y, ∃ M : MChart Y, v y ∈ M.U := by
    refine ⟨fun h y => ?_, GlobalTheory.T.polarization_pull_isLineBundle Y m DY v⟩
    obtain ⟨J, hJ⟩ := TopologicalSpace.Opens.mem_iSup.1 (h.cover.ge (Set.mem_univ y))
    have h1 := LB.wchart_le _ _ J PUnit.unit hJ
    exact ⟨(J PUnit.unit).1 PUnit.unit, LB.wchart_le _ _ _ PUnit.unit h1.1⟩
  have cov : (∀ y, ∃ M' : MChart Y', y ∈ M'.U) ↔ ∀ y, ∃ M : MChart Y, v y ∈ M.U :=
    ⟨fun h y => let ⟨M', hM'⟩ := h y; GlobalTheory.T.exists_chart_of_open_immersion_image Y Y' v hv hm M' y hM',
      fun h y => let ⟨M, hM⟩ := h y; GlobalTheory.T.exists_chart_of_open_immersion_preimage Y Y' v hv hm M y hM⟩
  constructor
  · intro h
    have h2 : ((polOf Y m DY).pull v).IsLB := lbY.2 (cov.1 (lbY'.1 h.isLB))
    exact h.of_lbIso h2 (LBIso.symm (GlobalTheory.T.polarization_comap_open_immersion Y Y' v DY DY' m hv hm hI h2 h.isLB))
  · intro h
    have h2 := lbY'.2 (cov.2 (lbY.1 h.isLB))
    exact h.of_lbIso h2 (GlobalTheory.T.polarization_comap_open_immersion Y Y' v DY DY' m hv hm hI h.isLB h2)

end GlobalTheory.PolOpen
