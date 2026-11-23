import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumSquaresRightDerivPowDifferentialOperatoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApOpAddSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakSolutionOfSmoothSolutionStatement
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem exists_apOp_add_lower_sum {d : ℕ} (U : Set (E d)) (k : ℕ)
    (A : ℕ → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hA : ∀ i n w, ContDiffOn ℝ ∞ (A i n w) U) (t : ℕ → ℂ) :
    ∀ N ≤ k, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) U) ∧
      (∀ x ξ : E d, symb (2 * k) a x ξ = symb (2 * k) (A k) x ξ) ∧
      ∀ (u : E d → ℂ) (x : E d), apOp (2 * k) a u x =
        apOp (2 * k) (A k) u x + ∑ i ∈ Finset.range N, t i * apOp (2 * i) (A i) u x := by
  intro N
  induction N with
  | zero => intro _; exact ⟨A k, hA k, fun _ _ => rfl, fun u x => by simp⟩
  | succ N ih =>
    intro hN
    obtain ⟨a, ha, hs, hop⟩ := ih (by omega)
    obtain ⟨a'', h1, h2, h3⟩ :=
      GlobalTheory.T.exists_apOp_add_smul' d (2 * k) (2 * N) U a (A N) (t N) (by omega) ha (hA N)
    refine ⟨a'', h1, fun x ξ => ?_, fun u x => ?_⟩
    · rw [h2, if_neg (by omega), add_zero, hs]
    · rw [h3, hop, Finset.sum_range_succ]; ring

theorem exists_elliptic_weakSol_of_aeval_eq_zero : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r, hr, c, hc, hspan, hder⟩ := GlobalTheory.T.leftInvariantVectorFields_expCoords_smooth_frame 𝔸 G 𝔤 h d b
  choose A hAs hAsymb hAop using GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator 𝔸 G 𝔤 h d b r c ⟨hc, hspan, hder⟩
  obtain ⟨a, ha, hsa, hopa⟩ := exists_apOp_add_lower_sum (Metric.ball (0 : E d) r) P.natDegree A
    (fun i => hAs i) (fun i => P.coeff i) P.natDegree le_rfl
  refine ⟨r, hr, 2 * P.natDegree, a, ha, ?_, ?_⟩
  · intro x hx ξ hξ
    rw [hsa, hAsymb]
    obtain ⟨i, hi⟩ := hspan x hx ξ hξ
    have hpos : 0 < ∑ i, (∑ j, c (b i) j x * ξ j) ^ 2 :=
      lt_of_lt_of_le (by positivity : 0 < (∑ j, c (b i) j x * ξ j) ^ 2)
        (Finset.single_le_sum (f := fun i => (∑ j, c (b i) j x * ξ j) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    exact_mod_cast (pow_pos hpos P.natDegree).ne'
  · intro f hf g
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h f g
    set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔdef
    have hΔ : Δ ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩))
    have hmem : Polynomial.aeval Δ P ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ Δ)
    have hzero : ∀ y, (Polynomial.aeval Δ P f' : G → ℂ) y = 0 := by
      intro y; rw [hf'2 _ hmem y, hf]; rfl
    have hu : (fun y : E d => (f : G → ℂ) (g * h.expG (coordEquiv b y))) =
        fun y => (f' : G → ℂ) (h.expG (coordEquiv b y)) := by
      funext y; rw [hf'1]
    refine GlobalTheory.T.weakSolution_of_smooth_solution d (2 * P.natDegree) (Metric.ball 0 r) Metric.isOpen_ball a ha _
      (h.contDiff_comp_coordEquiv f.2 g b).contDiffOn ?_
    intro x hx
    rw [hopa, hu]
    have key := hzero (h.expG (coordEquiv b x))
    rw [Polynomial.aeval_eq_sum_range] at key
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply] at key
    rw [← key, Finset.sum_range_succ _ P.natDegree, hP.coeff_natDegree, one_mul, add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hAop i f' x hx]
    · rw [hAop P.natDegree f' x hx]

end GlobalTheory.HCA
