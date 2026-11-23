import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem ModelCurveNum.proof (hN : CurveNumModel.Statement) : ModelCurveNum.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hb
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hm β
  have hQ' : BundleRealises y' k₀' Q β' := fun c => (hQ c).trans (hs c)
  have h1 := hN F K ι Ω y k₀ N e _ rfl hm Q β hQ W hW hle hrel
  have h2 := hN F K' ι' Ω y' k₀' N e' _ hx hm' Q β' hQ' W' hW' hle' hrel'
  have hc : W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      W'.comap (rename fun a : Fin (N + 1) => (⟨k₀', e'.symm a⟩ : Σ k, ι' k)) := by
    ext p
    have := SetLike.ext_iff.mp hb (rename (fun a : Fin (N + 1) => (⟨(), a⟩ : Σ _ : Unit, Fin (N + 1))) p)
    simp only [baseComap, Ideal.mem_comap, rename_rename] at this
    exact this
  rw [h1, h2, hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
