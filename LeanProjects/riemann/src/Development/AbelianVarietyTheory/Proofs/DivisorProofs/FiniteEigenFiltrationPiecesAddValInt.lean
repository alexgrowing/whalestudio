import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbFin

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
  [DecidableEq S]

theorem monic_prod (a : S → Int0 v) : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

def powBasis (a : S → Int0 v) : PowerBasis (Int0 v) (RS a) := AdjoinRoot.powerBasis' (monic_prod a)

instance finite_RS (a : S → Int0 v) : Module.Finite (Int0 v) (RS a) := (powBasis a).finite

theorem eq_zero_of_smul_RS (a : S → Int0 v) {c : Int0 v} (hc : c ≠ 0) {y : RS a}
    (h : c • y = 0) : y = 0 := by
  have b := (powBasis a).basis
  apply b.repr.injective
  refine Finsupp.ext fun i => ?_
  have h2 := congrArg (fun z => b.repr z i) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.1 h2).resolve_left hc

theorem eq_zero_of_smul_pi (a : S → Int0 v) {N : ℕ} {c : Int0 v} (hc : c ≠ 0)
    {y : Fin N → RS a} (h : c • y = 0) : y = 0 := by
  funext i
  have h3 := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply] at h3
  exact eq_zero_of_smul_RS a hc h3

theorem sat_kerMul (a : S → Int0 v) (r : RS a) (Q : Type) [AddCommGroup Q] [Module (RS a) Q]
    [Module (Int0 v) Q] [IsScalarTower (Int0 v) (RS a) Q]
    (htf : ∀ (c : Int0 v) (y : Q), c ≠ 0 → c • y = 0 → y = 0) :
    GlobalTheory.IsSaturatedSubmodule (kerMul a r Q) := by
  rw [GlobalTheory.isSaturatedSubmodule_iff]
  intro c hc x hx
  simp only [kerMul, Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
  rw [smul_comm] at hx
  exact htf c _ hc hx

theorem finite_main : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  intro C _ v S _ _ a _ N Fil hFil τ
  have hsatF : GlobalTheory.IsSaturatedSubmodule (Fil.restrictScalars (Int0 v)) :=
    GlobalTheory.isSaturatedSubmodule_iff.2 fun c hc x hx => hFil c x hc hx
  have hT1 : ∀ (c : Int0 v) (y : Fin N → RS a), c ≠ 0 → c • y = 0 → y = 0 :=
    fun c y hc h => eq_zero_of_smul_pi a hc h
  have hT2 : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := fun c y hc h =>
    Subtype.ext (hT1 c y hc (congrArg Subtype.val h))
  have hT3 : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hFil c x hc h
  have hF : Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) := hsatF.finite_of_valuationRing
  have hFil' : Module.Finite (Int0 v) Fil := hF
  have hQ : Module.Finite (Int0 v) ((Fin N → RS a) ⧸ Fil) :=
    Module.Finite.of_surjective (proj a Fil) (Submodule.mkQ_surjective Fil)
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsatF.comap (mulR a N (lin a τ))).finite_of_valuationRing
  · refine (hsatF.inf ?_).finite_of_valuationRing
    exact sat_kerMul a (cofac a τ) (Fin N → RS a) hT1
  · exact (sat_kerMul a (lin a τ) (Fin N → RS a) hT1).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) _ hT3).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) Fil hT2).finite_of_valuationRing
  · exact (sat_kerMul a (cofac a τ) Fil hT2).finite_of_valuationRing

end GlobalTheory.HerbFin
