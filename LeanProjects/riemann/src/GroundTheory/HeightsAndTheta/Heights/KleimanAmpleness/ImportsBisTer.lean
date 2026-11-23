import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)

theorem RealiseRestrict.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement)
    (hR : ResidueMap.Statement) (hRG : ResidueGen.Statement) (hC : RestrictGen.Statement) :
    RealiseRestrict.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy Q β hQ K' _ _ y' hy' hI hxy
  subst hx
  obtain ⟨Q'', hQ''⟩ := BundleOfDeg.full F K ι K' y' k₀ N e hy' β
  obtain ⟨ca, hca⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨cb, hcb⟩ := Kleiman.Generated.full F K' N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) Q''
  obtain ⟨cg, hcg⟩ := hG F K ι Ω y k₀ hy β
  obtain ⟨c, hcA, hcB, hcG⟩ : ∃ c, ca ≤ c ∧ cb ≤ c ∧ cg ≤ c :=
    ⟨max ca (max cb cg), by omega, by omega, by omega⟩
  obtain ⟨R, σ, hfr, hblk, hch⟩ := hR F K ι Ω y K' y' hI
  choose d₀ hd₀ using hy'.1
  obtain ⟨ρ, hρ1, hρ2⟩ := hRG F K ι Ω y K' y' hI R σ hfr hch (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (hcg c hcG) d₀ hd₀

  have hT : ∀ t : K', t ∈ secOver F y' (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm),
        t ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
          (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := by
    intro t
    have h := hS F K ι K' y' k₀ N e _ rfl hy' (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) 0 t
    simp only [PowRealises.twistMod_zero, mul_one, Submodule.mem_iInf, Submodule.restrictScalars_mem,
      neg_zero, zpow_zero] at h
    rw [h, PowRealises.mem_secOver]
    refine forall_congr' fun cc => forall_congr' fun hc => ?_
    rw [hρ2 cc hc, PowRealises.mem_span_inv_iff _
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))]
  have hQgen : ∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
        (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := fun I => by
    rw [← hca c hcA I, hQ c]
  have hQ''gen : ∀ I, (Q''.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
        (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := fun I => by
    rw [← hcb c hcB I, hQ'' c]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hT t).mp ht I
    · rw [Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ((hT t).mpr fun J => Submodule.subset_span ht)

  have hfx : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
      aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g ≠ 0 →
      ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g ∈ R,
        σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) f /
          aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g := by
    intro f g m hf hg hg0
    obtain ⟨h, hh⟩ := hblk k₀ (rename e.symm f) (rename e.symm g) m hf.rename_isHomogeneous
      hg.rename_isHomogeneous (by rwa [aeval_rename])
    have ea : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm f) /
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm g) =
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g := by
      rw [aeval_rename, aeval_rename]
    refine ⟨ea ▸ h, ?_⟩
    have hsub : (⟨_, ea ▸ h⟩ : R) = ⟨_, h⟩ := Subtype.ext ea.symm
    rw [hsub, hh, aeval_rename, aeval_rename]
  have hw' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  obtain ⟨r, hr⟩ := hC F N Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) K' (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) hxy
    R σ hfx Q Q'' c (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ρ
    (∏ k, y ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k))
    (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) hw' hQgen hQ''gen hρ1
  exact ⟨Q'', r, hr, hQ''⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
