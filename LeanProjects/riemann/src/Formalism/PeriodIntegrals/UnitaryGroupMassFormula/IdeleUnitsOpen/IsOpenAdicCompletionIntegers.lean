import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExGen

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.IdeleUnitsOpenW

variable (L : Type) [Field L] [NumberField L]

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 L)) :
    IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := by
  have h : (v.adicCompletionIntegers L : Set (v.adicCompletion L)) =
      ((Valued.v : Valuation (v.adicCompletion L) _).integer : Set (v.adicCompletion L)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem isOpen_integralFinite :
    IsOpen {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} :=
  RestrictedProduct.isOpen_forall_mem (isOpen_adicCompletionIntegers L)

def integralAdeles : Set (AdeleRing (𝓞 L) L) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 L), Valued.v (x.2 v) ≤ 1}

theorem isOpen_integralAdeles : IsOpen (integralAdeles L) := by
  have h : integralAdeles L = Prod.snd ⁻¹'
      {f : FiniteAdeleRing (𝓞 L) L | ∀ v, f v ∈ v.adicCompletionIntegers L} := by
    ext x
    exact Iff.rfl
  rw [h]
  exact (isOpen_integralFinite L).preimage continuous_snd

theorem unitIdeles_eq :
    (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L)) =
      (fun u : Ideles L => (u : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L ∩
        (fun u : Ideles L => ((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) ⁻¹' integralAdeles L := by
  ext u
  constructor
  · intro hu
    have hu' : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1 := hu
    refine ⟨fun v => (hu' v).le, fun v => ?_⟩
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, hu' v, one_mul, map_one] at e
    exact e.le
  · rintro ⟨h1, h2⟩
    show ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1
    intro v
    have e := congrArg Valued.v (comp_mul_inv L u v)
    rw [map_mul, map_one] at e
    have hle1 : Valued.v ((u : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have hle2 : Valued.v (((u⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm hle1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e.symm
      _ ≤ Valued.v ((u : AdeleRing (𝓞 L) L).2 v) * 1 := by gcongr
      _ = _ := mul_one _

theorem openUnits : Formalism.L2.Host.CharEx.OpenUnits L := by
  show IsOpen (Formalism.L2.Host.CharEx.unitIdeles L : Set (Ideles L))
  rw [unitIdeles_eq]
  exact ((isOpen_integralAdeles L).preimage Units.continuous_val).inter
    ((isOpen_integralAdeles L).preimage (Units.continuous_val.comp continuous_inv))

end PI.IdeleUnitsOpenW
