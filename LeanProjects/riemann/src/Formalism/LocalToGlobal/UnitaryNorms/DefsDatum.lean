import Formalism.LocalToGlobal.UnitaryNorms.CharHost

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverPF (p : ℕ) (v : HeightOneSpectrum (𝓞 H.F)) : Prop := ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal

def PvSet (𝔭 : HeightOneSpectrum (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.F)) : Set (HeightOneSpectrum (𝓞 H.E)) :=
  {w | w ∈ aboveF (L := H.E) H.F v ∧ w.under (𝓞 H.K) = 𝔭}

structure PlacesOverCommonPrime where

  pK : HeightOneSpectrum (𝓞 H.K)

  pK' : HeightOneSpectrum (𝓞 H.K)
  pK_over : ((H.pde : ℕ) : 𝓞 H.K) ∈ pK.asIdeal
  pK'_over : ((H.pde' : ℕ) : 𝓞 H.K) ∈ pK'.asIdeal

  P : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde v → HeightOneSpectrum (𝓞 H.E)

  P' : ∀ v : HeightOneSpectrum (𝓞 H.F), OverPF H H.pde' v → HeightOneSpectrum (𝓞 H.E)

  P_mem : ∀ v hv, P v hv ∈ PvSet H pK v
  P'_mem : ∀ v hv, P' v hv ∈ PvSet H pK' v

structure ClsRepK where
  rep : ClassGroup (𝓞 H.K) → (nonZeroDivisors (Ideal (𝓞 H.K)))
  rep_cls : ∀ c, ClassGroup.mk0 (rep c) = c

variable {H}

def idK (p : ℕ) : Ideal (𝓞 H.K) := Ideal.span {((p : ℕ) : 𝓞 H.K)}

def PrimeToPl (𝔞 : Ideal (𝓞 H.K)) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ¬ 𝔞 ≤ (v.under (𝓞 H.K)).asIdeal

end Formalism.L2.Host
