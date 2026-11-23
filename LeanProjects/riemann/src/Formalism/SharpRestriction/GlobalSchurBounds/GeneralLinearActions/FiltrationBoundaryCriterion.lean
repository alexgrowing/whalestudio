import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

abbrev HH (D : D7) : Type := D.R.A

def hco (D : D7) (g : D.R.GG) : HH D := D.R.iotaInv g.2

def gOf (D : D7) (g₀ : G0) (h : HH D) : D.R.GG := (g₀, D.R.iota h)

def ordH {n : ℕ} (h : ZMod n) : ℕ := addOrderOf h

def rho (D : D7) (τ g : D.R.GG) : D.R.GG := D.R.cc * g * τ

def placeBelow {e : ℕ} (g : GG e) : GG e := if g.1.2 = 1 then g else cc e * g

open Classical in

def frob (D : D7) (p : ℕ) : D.R.GG :=
  if h : ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, ∃ P : Ideal (𝓞 D.host.E),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P
  then D.host.galE h.choose else 1

def hOf (e l : ℕ) : ZMod (2 ^ e) :=
  if h : Nat.Coprime l 2 then
    iotaHInv e (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) h)))
  else 0

abbrev ch (e : ℕ) : GG e →* ℤˣ := chD e

abbrev ps (e : ℕ) : GG e →* ℤˣ := chQ e

def sgc0 : G0 := ((-1 : ℤˣ), (1 : ℤˣ)) * c0

def chCx (e : ℕ) : GG e →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (ch e)

def PhiEmb (D : D7) : Set (D.host.E →+* ℂ) := D.host.emb '' (D.R.Psi : Set (D.R.GG))

def rdF (D : D7) : ℝ :=
  |(discr D.host.F : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.F : ℝ))

abbrev tops (D : D7) : Finset (D.R.GG) := D.host.topPlaces

abbrev thick (D : D7) : Finset (D.R.GG) := D.host.thickPlaces

end Formalism.MainNotions.GlobalTheoryTheory

end
