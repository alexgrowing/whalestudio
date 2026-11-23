import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachEtaleModuleFrobeniusBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGoodStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem psi_of_etale_basis {R E M Γ : Type*} [CommRing R] [CommRing E] [Algebra R E]
    [AddCommGroup M] [Module E M] [Module R M] [IsScalarTower R E M]
    (φE : E →+* E) (φD : M →ₗ[R] M) (hφD : ∀ (e : E) (x : M), φD (e • x) = φE e • φD x)
    (γE : Γ → E →+* E) (γD : Γ → M →ₗ[R] M)
    (hγD : ∀ g (e : E) (x : M), γD g (e • x) = γE g e • γD g x)
    (hφγ : ∀ g x, φD (γD g x) = γD g (φD x)) {r : ℕ} (b b' : Module.Basis (Fin r) E M)
    (hb : ∀ j, b' j = φD (b j)) (ψE : E →ₗ[R] E)
    (hψφ : ∀ a x, ψE (φE a * x) = a * ψE x) (hψγ : ∀ g x, ψE (γE g x) = γE g (ψE x))
    (hψone : ψE 1 = 1) :
    ∃ ψ : M →ₗ[R] M, (∀ x, ψ (φD x) = x) ∧
      (∀ (a : E) x, ψ (φE a • x) = a • ψ x) ∧ ∀ g x, ψ (γD g x) = γD g (ψ x) := by
  let ψ : M →ₗ[R] M :=
    { toFun := fun z => ∑ j, ψE (b'.repr z j) • b j
      map_add' := fun z w => by
        simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul E c z, map_smul, Finsupp.smul_apply, smul_eq_mul,
          ← Algebra.smul_def, map_smul, smul_assoc] }
  have hψ : ∀ z, ψ z = ∑ j, ψE (b'.repr z j) • b j := fun z => rfl
  have hdec : ∀ z : M, z = ∑ j, b'.repr z j • φD (b j) := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    simp only [hb]
  have hkey : ∀ (x : E) (y : M), ψ (x • φD y) = ψE x • y := by
    intro x y
    have hy : φD y = ∑ j, φE (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      rw [map_sum]
      simp only [hφD, hb]
    rw [hψ, hy, Finset.smul_sum]
    simp only [smul_smul]
    rw [b'.repr_sum_self]
    conv_rhs => rw [← b.sum_repr y, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, hψφ, smul_smul, mul_comm]
  refine ⟨ψ, fun x => ?_, fun a z => ?_, fun g z => ?_⟩
  · have := hkey 1 x
    rwa [one_smul, hψone, one_smul] at this
  · rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hψφ, mul_smul]
  · rw [hψ z, map_sum]
    conv_lhs => rw [hdec z, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hγD, ← hφγ, hkey, hψγ, hγD]

set_option maxHeartbeats 2000000 in

theorem psiD_exists : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  intro D HW F l _ K s LL h W T
  obtain ⟨r, b, b', hb⟩ := GlobalTheory.T.wachEtaleModule_frobenius_basis D HW F l K s LL h T
  obtain ⟨ψE, hψφ, hψγ, hψ1⟩ := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K s LL h
  have hψone : ψE 1 = 1 := by
    have := hψ1 0 (Fact.out : l.Prime).pos 1
    simpa using this
  exact psi_of_etale_basis (W.φE : W.EE →+* W.EE) (W.φD T) (W.φD_smul T)
    (fun g => (W.γE g : W.EE →+* W.EE)) (W.γD T) (W.γD_smul T) (W.φγ_comm T) b b' hb ψE hψφ hψγ hψone

end GlobalTheory
