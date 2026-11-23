import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplitAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.IdeleGroups.LocalNormGroups

noncomputable section

open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC UpperTheory.ConvolutionTheory.T

namespace UpperTheory.ConvolutionTheory.Sph.NormUnramified

private theorem loc_one_of {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem comp_norm_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (η : HChar F) (hη : IsNormChar E η) : ∀ x, η.1 (GroundTheory.Global.ideleNorm F E x) = 1 := by
  let ψ : HChar E := ⟨η.1.comp (GroundTheory.Global.ideleNorm F E), η.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg η.1 (GroundTheory.Global.ideleNorm_diagonal (K := F) k)).trans (η.2.2 _)⟩
  have hψ : ∀ x, ψ.1 x = η.1 (GroundTheory.Global.ideleNorm F E x) := fun _ => rfl
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ψ.val w = 1 := by
    filter_upwards [hη.2.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))] with w h1 h2
    have hf := GlobalTheory.ArtinTransport.normV_eq_pow (E := F) (E' := E) (v := w.under (𝓞 F)) (w := w) rfl
    obtain ⟨a, b⟩ := GlobalTheory.NormValGen.unrAt_val_of_comp_norm F E η ψ hψ w _ hf h2
    exact ⟨a, b.trans (h1 _ hf)⟩
  have h1 : ψ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ.1 ψ.2.1 ψ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of ψ w this.1 this.2 y
  intro x
  rw [← hψ, h1]; rfl

end UpperTheory.ConvolutionTheory.Sph.NormUnramified

open UpperTheory.ConvolutionTheory.Sph.NormUnramified in
theorem UpperTheory.ConvolutionTheory.Sph.normUnr :
    UpperTheory.ConvolutionTheory.Sph.NormUnr := by
  intro F E _ _ _ _ _ _ η hη v hu x hx
  obtain ⟨⟨w, hw⟩⟩ := GroundTheory.Global.nonempty_placesOver E v
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hw
  haveI := hw
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hu ⟨w, hw⟩)
  have hxu : x ∈ (Submonoid.ofClass ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletionIntegers F)).units := by
    have hx1 : Valued.v (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) = 1 := hx
    rw [Submonoid.mem_units_iff]
    refine ⟨hx1.le, ?_⟩
    change Valued.v ((x⁻¹ : _ˣ) : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx1, inv_one]
  obtain ⟨y, -, hy⟩ := GroundTheory.Global.IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one _ w he hxu
  have hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x :=
    Units.ext (by rw [GroundTheory.LocalField.coe_normUnits]; exact hy)
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 := comp_norm_eq_one η hη (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h2] at h3
  exact h3
