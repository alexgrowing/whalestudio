import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.RankDeRham

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in

theorem one_ne_zero_BdR : (1 : BdR) ≠ 0 := by
  intro h
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by rw [← mul_one (PD.ι PD.t), h, mul_zero]
  rw [this]
  exact Submodule.zero_mem _

include PD in

theorem eq_zero_of_tmul_one (v : V) (hv : v ⊗ₜ[Qp] (1 : BdR) = 0) : v = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero_BdR PD)
  have h := congrArg (fun x => TensorProduct.rid Qp V (LinearMap.lTensor V f x)) hv
  simpa [hf] using h

theorem finrank_H0V_le [FiniteDimensional LL ↥(DdR PD ρ)] :
    finrank LL ↥(H0V ρ) ≤ finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) := by
  haveI : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let j : V →ₗ[LL] V ⊗[Qp] BdR := (AlgebraTensorModule.mk Qp LL V BdR).flip 1
  have hj : ∀ v, j v = v ⊗ₜ[Qp] (1 : BdR) := fun v => rfl
  have hm : ∀ v ∈ H0V ρ, j v ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0 := by
    intro v hv
    refine ⟨?_, ?_⟩
    · simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hv
      have : j v ∈ DdR PD ρ := by
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero]
        intro g
        rw [hj]
        simp [actVdR, hv g]
      exact this
    · exact ⟨v ⊗ₜ[Qp] ⟨1, PD.one_mem⟩, by simp [hj]⟩
  refine LinearMap.finrank_le_finrank_of_injective (f := j.restrict hm) ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  have h0 : j v.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
  have := eq_zero_of_tmul_one PD v.1 (by rw [← hj]; exact h0)
  exact (Submodule.mem_bot _).2 (Subtype.ext this)

theorem h0_add_le [FiniteDimensional LL V] (hK : finrank Qp K = 1) (h : IsDR PD ρ) :
    (finrank LL ↥(H0V ρ) : ℤ) + ((finrank LL ↥(DdR PD ρ) : ℤ) -
      finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) ≤ finrank LL V := by
  have h' : finrank LL ↥(DdR PD ρ) = finrank LL V := by rw [h, hK, one_mul]
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · have := Submodule.finrank_le (H0V ρ)
    omega
  · haveI : FiniteDimensional LL ↥(DdR PD ρ) := Module.finite_of_finrank_pos (by omega)
    have := finrank_H0V_le PD ρ
    omega

end General

theorem finrank_H1f_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), finrank ℚ_[l] ↥K.1 = 1 → LocalSituation.bkAll (P.PD K) → ∀ A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsDR (P.PD K) A.ρ → finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) ≤ finrank ↥LL.1 A.V := by
  intro l _ P K LL hK hBK A hA
  have hd := hBK.2.1 _ _ (goodO_ringOfIntegers l LL) A hA
  have h := h0_add_le (P.PD K) A.ρ hK hA
  rw [← hd] at h
  exact_mod_cast h

end GlobalTheory.Pass.RankDeRham
