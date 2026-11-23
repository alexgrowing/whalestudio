import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite

noncomputable section

open scoped GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC UpperTheory.ConvolutionTheory.T

namespace UpperTheory.ConvolutionTheory.T.Ncs

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

private theorem norm_surj {A B : Type} [Field A] [Field B] [Algebra A B] (hs : Function.Surjective (algebraMap A B))
    (x : Aˣ) : ∃ y : Bˣ, GroundTheory.LocalField.normUnits A B y = x := by
  have hfr : Module.finrank A B = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap A B) ⟨(algebraMap A B).injective, hs⟩).finrank_eq
    simpa using this.symm
  refine ⟨Units.map (algebraMap A B).toMonoidHom x, Units.ext ?_⟩
  rw [GroundTheory.LocalField.coe_normUnits]
  change Algebra.norm A (algebraMap A B x) = x
  rw [Algebra.norm_algebraMap, hfr, pow_one]

private theorem loc_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (η : HChar F) (hη : IsNormChar E η) (v : HeightOneSpectrum (𝓞 F)) (hs : GM.Split E v)
    (x : (v.adicCompletion F)ˣ) : η.loc v x = 1 := by
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
  obtain ⟨⟨w, hw⟩⟩ := GroundTheory.Global.nonempty_placesOver E v
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hw
  haveI := hw
  have hsurj := hs ⟨w, hw⟩
  obtain ⟨y, hn⟩ := norm_surj (A := (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (B := w.adicCompletion E) hsurj x
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 : η.1 (GroundTheory.Global.ideleNorm F E (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)) = 1 := by
    rw [← hψ, h1]; rfl
  rw [h2] at h3
  exact h3

private theorem twist_inter {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (π : CuspSub F n) (η : HChar F)
    (v : HeightOneSpectrum (𝓞 F)) (h : ∀ x, η.loc v x = 1) (g : GL (Fin n) (v.adicCompletion F)) (φ : π.V) :
    (π.twist η).locRep v g (π.toTwist η φ) = π.toTwist η (π.locRep v g φ) := by
  have hd : CuspSub.locDet n η v g = 1 := h _
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, ← CuspSub.locRep_eq]
  simp only [opAdd, zero_smul, add_zero]
  have e : opMul η (Op.fin (locGL F n v g)) = 1 := (CuspSub.chiDet_locGL η v g).trans hd
  rw [e, Units.val_one, one_smul]

end UpperTheory.ConvolutionTheory.T.Ncs

open UpperTheory.ConvolutionTheory.T.Ncs in
theorem UpperTheory.ConvolutionTheory.T.normCharSplit :
    UpperTheory.ConvolutionTheory.T.NormCharSplit := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ η hη v hs π τ
  have hl := loc_eq_one η hη v hs
  change (π.twist η).IsLocComp v τ ↔ π.IsLocComp v τ
  constructor
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).symm.toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).symm.injective ?_),
      fun g x => (π.toTwist η).injective ?_⟩
    · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← twist_inter π η v hl, LinearEquiv.apply_symm_apply, hf]
  · rintro ⟨f, h0, hf⟩
    refine ⟨(π.toTwist η).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun x => (π.toTwist η).injective ?_),
      fun g x => ?_⟩
    · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h x
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [twist_inter π η v hl, hf]
