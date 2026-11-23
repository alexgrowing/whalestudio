import Mathlib
import Formalism.PeriodIntegrals.InfTypeChar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfinityTypeCharacter.ExtensionEmbeddingAlgebraMap

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.InfTypeCharW

variable {L : Type} [Field L] [NumberField L]

def projAt (w : InfinitePlace L) : AdeleRing (𝓞 L) L →+* w.Completion :=
  (Pi.evalRingHom (fun w : InfinitePlace L => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def compAt (w : InfinitePlace L) : Ideles L →* (w.Completion)ˣ := Units.map (projAt w).toMonoidHom

def ext (φ : L →+* ℂ) : (InfinitePlace.mk φ).Completion →+* ℂ := (exists_ext φ).choose

def chi (φ : L →+* ℂ) : Ideles L →* ℂˣ :=
  normalize.comp ((Units.map (ext φ).toMonoidHom).comp (compAt (InfinitePlace.mk φ)))

def Phi {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Ideles L →* ℂˣ where
  toFun x := ∏ i, chi (φ i) x ^ n i
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]

end PI.InfTypeCharW
