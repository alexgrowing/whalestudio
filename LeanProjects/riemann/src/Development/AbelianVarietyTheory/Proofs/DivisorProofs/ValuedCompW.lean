import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId

noncomputable section

namespace GlobalTheory.TateUnr

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def compW {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v) :
    idelesAt E (evFin F v) →* (w.adicCompletion E)ˣ :=
  (Units.map (toCompl hw).toMonoidHom).comp (idelesAtEquiv E v).toMonoidHom

def ordW {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v) (l : idelesAt E (evFin F v)) : ℤ :=
  -WithZero.log (Valued.v ((compW hw l : (w.adicCompletion E)ˣ) : w.adicCompletion E))

def ordV (v : Pl F) (l : idelesAt E (evFin F v)) : aboveF (L := E) F v → ℤ :=
  fun w => ordW (mem_aboveF.1 w.2) l

theorem compW_apply {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v) (l : idelesAt E (evFin F v)) :
    ((compW hw l : (w.adicCompletion E)ˣ) : w.adicCompletion E) = toCompl hw (compFin F E v (l.1 : AE F E)) := rfl

theorem valued_compW {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v) (l : idelesAt E (evFin F v)) :
    Valued.v ((compW hw l : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-ordW hw l) := by
  rw [ordW, neg_neg, WithZero.exp_log]
  exact (Valuation.ne_zero_iff _).2 (Units.ne_zero _)

theorem ordW_mul {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : w.under (𝓞 F) = v) (l m : idelesAt E (evFin F v)) :
    ordW hw (l * m) = ordW hw l + ordW hw m := by
  simp only [ordW, map_mul, Units.val_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)) ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))]
  ring

theorem ordV_mul (v : Pl F) (l m : idelesAt E (evFin F v)) : ordV v (l * m) = ordV v l + ordV v m :=
  funext fun w => ordW_mul _ l m

theorem ordV_inv (v : Pl F) (l : idelesAt E (evFin F v)) : ordV v l⁻¹ = -ordV v l := by
  have h := ordV_mul v l⁻¹ l
  rw [inv_mul_cancel] at h
  have h1 : ordV v (1 : idelesAt E (evFin F v)) = 0 := by
    have := ordV_mul (E := E) v 1 1
    rw [mul_one] at this
    funext w
    have := congrFun this w
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
    omega
  rw [h1] at h
  funext w
  have := congrFun h w
  simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at this ⊢
  omega

end GlobalTheory.TateUnr

end
