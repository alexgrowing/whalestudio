import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick

namespace UpperTheory.V.FW

abbrev Cl (K : Type) [Field K] [NumberField K] : Type := ClassGroup (𝓞 K)

section Cyc

variable (M : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]

def clA (t : (ZMod M)ˣ) : Cl L →* Cl L := clMap (sg M L t)⁻¹.toRingEquiv

def cycRep : Representation ℤ (ZMod M)ˣ (Additive (Cl L)) :=
  (clRep L).comp (((sg M L).toMonoidHom).comp invMonoidHom)

theorem cycRep_apply (t : (ZMod M)ˣ) (x : Cl L) :
    cycRep M L t (Additive.ofMul x) = Additive.ofMul (clA M L t x) := by
  rw [cycRep, MonoidHom.comp_apply, MonoidHom.comp_apply, invMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_inv, clRep_apply]
  rfl

def embT (φ : L →+* ℂ) (t : (ZMod M)ˣ) : L →+* ℂ := φ.comp (sg M L t).toRingEquiv.toRingHom

end Cyc

section Sign

variable {K ι : Type} [Field K] [NumberField K]

def sgn (e : ι → K →+* ℂ) (a : K) : ι → ZMod 2 := fun i => if (e i a).re < 0 then 1 else 0

def sgnE [IsCMField K] (e : ι → K →+* ℂ) : AddSubgroup (ι → ZMod 2) :=
  AddSubgroup.closure {f | ∃ u : (𝓞 K)ˣ, cE K ((u : 𝓞 K) : K) = ((u : 𝓞 K) : K) ∧ f = sgn e ((u : 𝓞 K) : K)}

variable (K) in

def UnrFin : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield K)) = 1

end Sign

end UpperTheory.V.FW

end
