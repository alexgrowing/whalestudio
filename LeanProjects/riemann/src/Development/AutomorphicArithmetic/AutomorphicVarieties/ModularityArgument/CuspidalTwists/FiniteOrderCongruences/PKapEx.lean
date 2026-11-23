import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.TwistIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NotLtOfCoprime
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormEqOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace KapEx

theorem norm_eq_one {l : ℕ} [Fact l.Prime] {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.Qk14.norm_eq_one h

def W (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {a | ‖(a : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    have e : (a : Qbar l) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ha)
    rw [norm_mul, norm_eq_one ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have ha0 : (a : Qbar l) ≠ 0 := a.ne_zero
    have e : ((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1 = -((a : Qbar l)⁻¹ * (a - 1)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, inv_mul_cancel₀ ha0, mul_one]
      ring
    rw [e, norm_neg, norm_mul, norm_inv, norm_eq_one ha, inv_one, one_mul]
    exact ha

theorem isOpen_kappaOpenNeighbourhood (l : ℕ) [Fact l.Prime] : IsOpen ((W l : Subgroup (Qbar l)ˣ) : Set (Qbar l)ˣ) := by
  show IsOpen {a : (Qbar l)ˣ | ‖(a : Qbar l) - 1‖ < 1}
  exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

theorem cong_of_mem {l : ℕ} [Fact l.Prime] {x : (Qbar l)ˣ} (hx : x ∈ W l) : Cong x 1 := by
  unfold Cong
  rw [Units.val_one]
  exact hx

theorem exists_pow_cong {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    {l : ℕ} [Fact l.Prime] (f : Γ →* (Qbar l)ˣ) (hf : Continuous f) : ∃ d : ℕ, 0 < d ∧ ∀ g, f g ^ d ∈ W l := by
  have hU : IsOpen (((W l).comap f : Subgroup Γ) : Set Γ) := (isOpen_kappaOpenNeighbourhood l).preimage hf
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  have hi : ((W l).comap f).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  refine ⟨((W l).comap f).index.factorial, Nat.factorial_pos _, fun g => ?_⟩
  rw [← map_pow]
  exact Subgroup.pow_mem_of_index_ne_zero_of_dvd hi g fun n h0 hn => Nat.dvd_factorial h0 hn

theorem cc_notMem {Ω : Type} [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsTotallyComplex K]
    {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm

end KapEx

end UpperTheory.V.Cu2

end
