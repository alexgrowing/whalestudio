import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocusStatement

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem sdRep_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  intro h M d hh hM hodd hd hcop
  obtain ⟨O, _, bar, r, eO, W, d₀, e, jl, n, o, κ, hbar, hspan, hW, hd₀, hsum, hee, hex, huniq⟩ :=
    GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled h M d hh hM hodd hd hcop
  obtain ⟨H, sH, zH, actH, hpr, hra, hadj, hq, hln, hrep⟩ :=
    GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction (8 * h) M (by omega) hM hodd O bar r eO W d₀ hbar hspan hW hd₀ hsum
  obtain ⟨Y, j, c, hj, hjq, hker, hunit, hpull, huniv⟩ :=
    GlobalTheory.T.siegel_family_idempotent_image_open_locus h (8 * h) M d O bar e jl n o κ H sH zH actH hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨Y, j ≫ sH, c, hker, hunit, isQProjOver_comp_immersion j sH hj hjq hq, ?_⟩
  intro S t c' hdu hc'
  obtain ⟨z', act', hz'p, hz'r, hz'a, hz'rel⟩ := hex S t c' hdu hc'
  obtain ⟨g, ⟨hg, hgpb⟩, -⟩ := hrep S t z' act' hz'p hz'r hz'a
  obtain ⟨y, ⟨hy, hyc⟩, -⟩ := huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hg], hyc⟩, ?_⟩
  rintro f ⟨hf, hfc⟩
  obtain ⟨w, actw, hwp, hwr, hwa, hwpb, hwrel⟩ := hpull S t f c' hf hfc
  have hiso := huniq S t c' w z' actw act' hdu hc' hwp hz'p hwr hz'r hwa hz'a hwrel hz'rel
  have h2 : ActPB w actw zH actH (𝟙 S ≫ g) := hiso.trans hgpb
  rw [Category.id_comp] at h2
  have hfj : f ≫ j = g :=
    (hrep S t w actw hwp hwr hwa).unique ⟨by rw [Category.assoc]; exact hf, hwpb⟩ ⟨hg, h2⟩
  exact (huniv S t g c' hg hdu hc' ⟨z', act', hgpb, hz'rel⟩).unique ⟨hfj, hfc⟩ ⟨hy, hyc⟩

end GlobalTheory.UPel.HT
