import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct

open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ConjSat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem locU_eq_of_under {w u : HeightOneSpectrum (𝓞 E)}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : locU n u = locU n w := by
  simp only [locU, h]

abbrev flipGL (w : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E) ≃* GL (Fin n) (w.adicCompletion E) :=
  GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n

theorem flipGL_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)) :
    flipGL w g = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem continuous_flipGL (w : HeightOneSpectrum (𝓞 E)) : Continuous (flipGL (n := n) w) := by
  have : (flipGL (n := n) w : _ → _) = fun g => GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
    funext (flipGL_eq w)
  rw [this]
  exact (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem cLoc_eq_flipGL (x : UA E n) (w : HeightOneSpectrum (𝓞 E)) :
    cLoc w x = flipGL w (cLoc (GlobalTheory.ThetaSatake.cw w) x) :=
  (GlobalTheory.BCT.LocCpt.cLoc_eq_invT x w).trans (flipGL_eq w _).symm

def flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) : SmIrr (GLw n (GlobalTheory.ThetaSatake.cw w)) where
  V := σ.V
  ρ := σ.ρ.comp (flipGL w).toMonoidHom
  smooth v := (σ.smooth v).preimage (continuous_flipGL w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (flipGL w).surjective σ.irred

theorem hasSatGL_flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) {B : Multiset ℂˣ}
    (h : HasSatGL w σ.ρ B) : HasSatGL (GlobalTheory.ThetaSatake.cw w) (flipIrr σ).ρ (B.map (·⁻¹)) := by
  refine GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w).symm (fun a => ?_)
    (GlobalTheory.ThetaSatake.absNorm_cw w) (LinearEquiv.refl ℂ σ.V) (fun g x => ?_) h
  · have := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w).2.2 ((GlobalTheory.ThetaSatake.cloc w).symm a)
    exact (this.symm.trans (congrArg _ ((GlobalTheory.ThetaSatake.cloc w).apply_symm_apply a)))
  · change σ.ρ (flipGL w ((flipGL w).symm g)) x = σ.ρ g x
    rw [MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.ConjSat

open GlobalTheory.CompanionTheory.ConjSat in

theorem GlobalTheory.CompanionTheory.ConjSat.satConj : PositivityTheory.Rg.BcB.F.RS.SatConj := by
  intro E _ _ _ n π w u B _ _ hc ⟨σ, ⟨hirr, f, f0, hf, hfx⟩, hB⟩
  obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
  refine ⟨flipIrr σ, ⟨(flipIrr σ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr σ hB⟩
  have hx : (x : UA E n) ∈ locU n w := locU_eq_of_under hc.1 ▸ x.2
  have := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at this
  change f (σ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact this

end
