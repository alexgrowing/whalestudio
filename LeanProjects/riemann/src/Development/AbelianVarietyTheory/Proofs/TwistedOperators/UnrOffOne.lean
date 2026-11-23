import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, PP.under (𝓞 D.host.F) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
