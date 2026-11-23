import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.EntriesLat

noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

variable (I : AutInst)

instance instIsModuleTopologyT :
    IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) := ⟨rfl⟩

instance instContinuousAddT : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) _

instance instContinuousSMulT :
    ContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  IsModuleTopology.toContinuousSMul _ _

theorem exists_not_mem_range : ∃ x : I.E, x ∉ Set.range (algebraMap I.F I.E) := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (Algebra.linearMap I.F I.E) := fun x => by
    obtain ⟨a, ha⟩ := h x
    exact ⟨a, ha⟩
  have e := (LinearEquiv.ofBijective (Algebra.linearMap I.F I.E)
    ⟨(algebraMap I.F I.E).injective, hs⟩).finrank_eq
  rw [I.cm.deg2] at e
  rw [Module.finrank_self] at e
  omega

private theorem exists_nat_mul_lemma {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ d : ℕ, 1 ≤ d ∧ (d : E) * x ∈ Formalism.UG.intOE E := by
  have H : ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * x) := by
    have hq : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) x hq
    exact ⟨m, nonZeroDivisors.coe_ne_zero m, by rw [← zsmul_eq_mul]; exact hm⟩
  obtain ⟨y, hy0, hint⟩ := H
  have hmem : (y : E) * x ∈ Formalism.UG.intOE E :=
    RingHom.mem_range.2 ((IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem
  · refine ⟨n, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hy0), ?_⟩
    simpa using hmem

theorem exists_beta : ∃ β : I.E, β ∈ Formalism.UG.intOE I.E ∧ β ∉ Set.range (algebraMap I.F I.E) := by
  obtain ⟨x, hx⟩ := exists_not_mem_range I
  obtain ⟨d, hd, hdx⟩ := exists_nat_mul_lemma x
  have hd0 : (d : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨(d : I.E) * x, hdx, fun ⟨a, ha⟩ => hx ⟨a / d, ?_⟩⟩
  rw [map_div₀, map_natCast, ha]
  exact mul_div_cancel_left₀ x hd0

def beta : I.E := (exists_beta I).choose

theorem beta_mem : beta I ∈ Formalism.UG.intOE I.E := (exists_beta I).choose_spec.1

theorem beta_not_mem : beta I ∉ Set.range (algebraMap I.F I.E) := (exists_beta I).choose_spec.2

theorem linearIndependent_one_beta : LinearIndependent I.F ![(1 : I.E), beta I] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply beta_not_mem I
    refine ⟨-s / t, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht' : algebraMap I.F I.E t ≠ 0 := (map_ne_zero _).2 ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst

def basisE : Module.Basis (Fin 2) I.F I.E :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_beta I)
    (by rw [Fintype.card_fin, I.cm.deg2])

theorem basisE_apply (k : Fin 2) : basisE I k = ![(1 : I.E), beta I] k := by
  simp [basisE]

theorem basisE_mem (k : Fin 2) : basisE I k ∈ Formalism.UG.intOE I.E := by
  rw [basisE_apply]
  fin_cases k
  · exact one_mem _
  · exact beta_mem I

def basisT : Module.Basis (Fin 2) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (basisE I)

def coord (k : Fin 2) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) →ₗ[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F :=
  (basisT I).coord k

theorem sum_coord (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    ∑ k, coord I k t ⊗ₜ[I.F] basisE I k = t := by
  conv_rhs => rw [← (basisT I).sum_repr t]
  simp [coord, basisT, Module.Basis.coord_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul']

theorem continuous_coord (k : Fin 2) : Continuous (coord I k) := by
  haveI : Module.Finite (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) := Module.Finite.of_basis (basisT I)
  exact IsModuleTopology.continuous_of_linearMap (coord I k)

theorem thetaV_eq (v : InfinitePlace I.F) (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    thetaV I v t = ∑ k, evV I v (coord I k t) * I.φ v (basisE I k) := by
  conv_lhs => rw [← sum_coord I t]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

theorem tauF_eq (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I t = ∑ k, basisE I k ⊗ₜ[I.F] (coord I k t).2 := by
  conv_lhs => rw [← sum_coord I t]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show (1 : I.E) ⊗ₜ[I.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F (coord I k t) *
      (basisE I k ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

end PI.InvTopW
