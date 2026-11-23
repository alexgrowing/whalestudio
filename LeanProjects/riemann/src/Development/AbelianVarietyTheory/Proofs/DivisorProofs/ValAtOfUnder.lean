import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.UnrTate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

def valAt (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (y : Fv F v ⊗[F] E) : WithZero (Multiplicative ℤ) :=
  if h : w.under (𝓞 F) = v then Valued.v (toCompl h y) else 1

def ordAt (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (x : (Fv F v ⊗[F] E)ˣ) : ℤ := -WithZero.log (valAt v w x.1)

theorem valAt_of_under {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (y : Fv F v ⊗[F] E) :
    valAt v w y = Valued.v (toCompl h y) := dif_pos h

theorem valAt_ne_zero (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (x : (Fv F v ⊗[F] E)ˣ) : valAt v w x.1 ≠ 0 := by
  unfold valAt
  split_ifs with h
  · exact (Valuation.ne_zero_iff _).2 (x.isUnit.map (toCompl h)).ne_zero
  · exact one_ne_zero

theorem valAt_eq_exp (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (x : (Fv F v ⊗[F] E)ˣ) :
    valAt v w x.1 = WithZero.exp (-ordAt v w x) := by
  rw [ordAt, neg_neg, WithZero.exp_log (valAt_ne_zero v w x)]

theorem valAt_mul (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (y z : Fv F v ⊗[F] E) :
    valAt v w (y * z) = valAt v w y * valAt v w z := by
  unfold valAt
  split_ifs with h
  · rw [map_mul, map_mul]
  · rw [mul_one]

theorem ordAt_mul (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (x y : (Fv F v ⊗[F] E)ˣ) :
    ordAt v w (x * y) = ordAt v w x + ordAt v w y := by
  have h := valAt_mul v w x.1 y.1
  rw [← Units.val_mul, valAt_eq_exp, valAt_eq_exp, valAt_eq_exp, ← WithZero.exp_add] at h
  have := WithZero.exp_injective h
  linarith

theorem ordAt_one (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) : ordAt v w (1 : (Fv F v ⊗[F] E)ˣ) = 0 := by
  have h := ordAt_mul v w 1 1
  rw [mul_one] at h
  linarith

theorem ordAt_inv (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (x : (Fv F v ⊗[F] E)ˣ) : ordAt v w x⁻¹ = -ordAt v w x := by
  have h := ordAt_mul v w x x⁻¹
  rw [mul_inv_cancel, ordAt_one] at h
  linarith

def ordHom (v : Pl F) :
    (Fv F v ⊗[F] E)ˣ →* Multiplicative (Formalism.L2.Host.aboveF (L := E) F v → ℤ) where
  toFun x := Multiplicative.ofAdd fun w => ordAt v w.1 x
  map_one' := by
    rw [← ofAdd_zero]
    exact congrArg Multiplicative.ofAdd (funext fun w => ordAt_one v w.1)
  map_mul' x y := by
    rw [← ofAdd_add]
    exact congrArg Multiplicative.ofAdd (funext fun w => ordAt_mul v w.1 x y)

theorem valAt_one_tmul (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (b : Eˣ) :
    valAt v w ((Units.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toMonoidHom b : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) =
      Valued.v (algebraMap E (w.adicCompletion E) b) := by
  rw [valAt_of_under h]
  show Valued.v (toCompl h ((1 : Fv F v) ⊗ₜ[F] (b : E))) = _
  rw [toCompl_tmul, map_one, one_mul]

end GlobalTheory.UnrTate

end
