import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly

noncomputable section

lemma exists_perm_of_sum_single {d : ℕ} {τ τ' : Fin d → Option (Fin 3)}
    (h : ∑ t, Finsupp.single (τ t) (1 : ℕ) = ∑ t, Finsupp.single (τ' t) (1 : ℕ)) :
    ∃ π : Equiv.Perm (Fin d), ∀ t, τ' (π t) = τ t := by
  classical
  have hc : ∀ o : Option (Fin 3), Fintype.card {t // τ t = o} = Fintype.card {t // τ' t = o} := by
    intro o
    have h1 := congrArg (fun f => f o) h
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h1
  exact ⟨Equiv.ofFiberEquiv (fun o => Fintype.equivOfCardEq (hc o)), fun t => Equiv.ofFiberEquiv_map _ t⟩

lemma prod_X_eq_monomial {d : ℕ} (τ : Fin d → Option (Fin 3)) :
    (∏ t, (X (τ t) : MvPolynomial (Option (Fin 3)) ℝ)) =
      monomial (∑ t, Finsupp.single (τ t) (1 : ℕ)) 1 := by
  exact (monomial_sum_one (R := ℝ) Finset.univ fun t => Finsupp.single (τ t) 1).symm

lemma linear_form_add_eq_sum (n : Fin 3 → ℝ) (v : ℝ) :
    lin4 n + C v * X none =
      ∑ j : Option (Fin 3), C (Option.elim j v n) * (X j : MvPolynomial (Option (Fin 3)) ℝ) := by
  simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Fintype.sum_option, Option.elim_none,
    Option.elim_some]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_functional : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
    ∃ L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ, ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)) := by
  classical
  intro d T H
  obtain ⟨Λ, hΛ, hsym⟩ := (PositivityTheory.Xgp.t_fib_mdisc d).2
  obtain ⟨M, hM⟩ : ∃ M : Option (Fin 3) → Matrix (Fin d) (Fin d) ℂ, M none = H ∧ ∀ i, M (some i) = T i :=
    ⟨fun j => Option.elim j H T, rfl, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : (Option (Fin 3) →₀ ℕ) → ℂ, ∀ τ : Fin d → Option (Fin 3),
      g (∑ t, Finsupp.single (τ t) (1 : ℕ)) = (d.factorial : ℂ) * Λ (fun t => M (τ t)) := by
    refine ⟨fun m => if h : ∃ τ : Fin d → Option (Fin 3), ∑ t, Finsupp.single (τ t) (1 : ℕ) = m then
      (d.factorial : ℂ) * Λ (fun t => M (h.choose t)) else 0, fun τ => ?_⟩
    have h : ∃ τ' : Fin d → Option (Fin 3),
        ∑ t, Finsupp.single (τ' t) (1 : ℕ) = ∑ t, Finsupp.single (τ t) (1 : ℕ) := ⟨τ, rfl⟩
    simp only [dif_pos h]
    obtain ⟨π, hπ⟩ := exists_perm_of_sum_single h.choose_spec
    have e : (fun t => M (h.choose t)) = (fun t => M (τ t)) ∘ π :=
      funext fun t => by simp only [Function.comp_apply, hπ]
    rw [e, hsym]
  refine ⟨(basisMonomials (Option (Fin 3)) ℝ).constr ℝ g, fun c v => ?_⟩
  have hL : ∀ (m : Option (Fin 3) →₀ ℕ) (x : ℝ),
      (basisMonomials (Option (Fin 3)) ℝ).constr ℝ g (monomial m x) = (x : ℂ) * g m := by
    intro m x
    have hx : (monomial m x : MvPolynomial (Option (Fin 3)) ℝ) = x • basisMonomials (Option (Fin 3)) ℝ m := by
      simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [hx, map_smul, Module.Basis.constr_basis, Complex.real_smul]
  have hrow : ∀ t, (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H =
      ∑ j : Option (Fin 3), ((Option.elim j (v t) (c t) : ℝ) : ℂ) • M j := by
    intro t
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, hM.1, hM.2]
    exact add_comm _ _
  have hprod : (∏ t, (lin4 (c t) + C (v t) * X none) : MvPolynomial (Option (Fin 3)) ℝ) =
      ∑ r : Fin d → Option (Fin 3),
        monomial (∑ t, Finsupp.single (r t) (1 : ℕ)) (∏ t, Option.elim (r t) (v t) (c t)) := by
    simp only [linear_form_add_eq_sum]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ), prod_X_eq_monomial,
      C_mul_monomial, mul_one]
  simp only [hrow]
  rw [← hΛ, MultilinearMap.map_sum, hprod, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ, hL, hg, smul_eq_mul, Complex.ofReal_prod]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN.MdiscPoly
