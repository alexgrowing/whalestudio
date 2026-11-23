import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.UnitOpen

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_val_le (v : HeightOneSpectrum (𝓞 L)) (m : ℤ) :
    IsOpen {x : v.adicCompletion L | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective L (WithZero.exp (-m))
  have h : IsOpen (v.adicCompletionIntegers L : Set (v.adicCompletion L)) := Valued.isOpen_valuationSubring _
  convert h.preimage (continuous_mul_const p) using 1
  ext x
  show _ ↔ Valued.v (x * p) ≤ 1
  rw [map_mul, hp, WithZero.exp_neg, mul_inv_le_iff₀ (WithZero.exp_pos), one_mul]
  rfl

theorem continuous_comp (v : HeightOneSpectrum (𝓞 L)) :
    Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 v :=
  (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)

theorem isOpen_unitIdl : IsOpen (unitIdl L : Set (Ideles L)) := by
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 L) L | ∀ v, a v ∈ v.adicCompletionIntegers L} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have c1 : Continuous fun a : Ideles L => (a : AdeleRing (𝓞 L) L).2 := continuous_snd.comp Units.continuous_val
  have c2 : Continuous fun a : Ideles L => ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hV.preimage c1).inter (hV.preimage c2) using 1
  ext a
  constructor
  · intro ha
    exact ⟨fun v => (ha v).le, fun v => ((unitIdl L).inv_mem ha v).le⟩
  · rintro ⟨h1, h2⟩ v
    have h : (a : AdeleRing (𝓞 L) L).2 v * ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 L) L => z.2 v) a.mul_inv
    have h3 := congrArg (Valued.v : Valuation (v.adicCompletion L) _) h
    rw [map_mul, map_one] at h3
    have k1 : Valued.v ((a : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h1 v
    have k2 : Valued.v (((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) ≤ 1 := h2 v
    refine le_antisymm k1 ?_
    rw [← h3]
    exact mul_le_of_le_one_right' k2

open Classical in

theorem unit_open_and_congr_open : ∀ (L : Type) [Field L] [NumberField L], IsOpen (unitIdl L : Set (Ideles L)) ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), IsOpen {a : Ideles L | a ∈ unitIdl L ∧ ∀ v ∈ S, Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))} := by
  intro L _ _
  refine ⟨isOpen_unitIdl, fun S n => ?_⟩
  have h : IsOpen (⋂ v ∈ S, {a : Ideles L | Valued.v ((a : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))}) :=
    isOpen_biInter_finset fun v _ => (isOpen_val_le v _).preimage ((continuous_comp v).sub continuous_const)
  convert isOpen_unitIdl.inter h using 1
  ext a
  simp

end GlobalTheory.Mem.UnitOpen
