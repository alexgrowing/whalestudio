import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuLocal

open Formalism.L2.Host GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnitAt_of_valuation (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (h : ValuativeRel.valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1) : IsUnitAt w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 := GlobalTheory.SmGL.ord_eq_zero_iff.2 h
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at h1
  rw [IsUnitAt, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem loc_eq_unrChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) :
    χ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ.val w) :=
  GlobalTheory.PrinSat.eq_unrChar_of_ord (fun x hx => h x (isUnitAt_of_valuation w x hx)) (GlobalTheory.PrinSat.ord_unif w)

theorem loc_pow (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (x : (w.adicCompletion E)ˣ) :
    (χ ^ k).loc w x = χ.loc w x ^ k := by
  induction k with
  | zero => simpa using HChar.loc_one w x
  | succ k ih => rw [pow_succ, HChar.loc_mul, ih, pow_succ]

theorem loc_mul_loc_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : GlobalTheory.BCT.IsMu μ e) (w : HeightOneSpectrum (𝓞 E))
    (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ) :
    μ.loc (GlobalTheory.ThetaSatake.cw w) x * μ.loc w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) = 1 := by
  have h1 := GlobalTheory.BCT.MuProps.mu_mul_conj h (Neutral.B1.localIdele E _ x)
  rw [GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.ThetaPull.conjAd_localIdele] at h1
  exact h1

theorem isUnitAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnitAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnitAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

theorem isUnifAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnifAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnifAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

end GlobalTheory.CompanionTheory.MuLocal

open GlobalTheory.CompanionTheory.MuLocal Formalism.L2.Host GlobalTheory.CuspRep in

theorem GlobalTheory.CompanionTheory.MuLocal.muLoc_holds : PositivityTheory.Rg.BcB.F.RS.MuLoc := by
  intro E _ _ _ _ μ e w hμ hun
  refine ⟨loc_eq_unrChar hun, fun k => ⟨fun x hx => ?_, ?_⟩, fun u _ hu => ?_⟩
  · rw [loc_pow, hun x hx, one_pow]
  · rw [HChar.val, HChar.locK, MonoidHom.comp_apply, loc_pow]
    rfl
  · obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hu
    have hc := loc_mul_loc_conj hμ w
    refine ⟨fun x hx => ?_, ?_⟩
    · have h2 := hc x
      rw [hun _ (isUnitAt_conj w x hx), mul_one] at h2
      exact h2
    · have h2 := hc (atFin (GlobalTheory.ThetaSatake.cw w) (unif (GlobalTheory.ThetaSatake.cw w)))
      rw [μ.val_eq hun _ (isUnifAt_conj w _ (unif_spec _))] at h2
      exact eq_inv_of_mul_eq_one_left h2

end
