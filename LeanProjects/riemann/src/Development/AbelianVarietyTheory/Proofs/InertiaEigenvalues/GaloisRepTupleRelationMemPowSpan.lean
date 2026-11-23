import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovKer

theorem kerB : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  intro l _ Γ _ a r m ρs c N cs hdiv happ G hG
  apply hdiv N G
  intro g

  have hk : ∀ k, ∑ h ∈ G.support, zOm l (G h) * trc (ρs k) (h * g) = 0 := by
    intro k
    have h0 := congrFun hG k
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, GlobalTheory.TraceConjugationCover.tup, Pi.zero_apply] at h0
    have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) =>
      (M * ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace) h0
    simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      Matrix.zero_mul, Matrix.trace_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  have htr : ((G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) *
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace =
      ∑ h ∈ G.support, zOm l (G h) * (trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)) := by
    have e2 : ∑ h ∈ G.support, zOm l (G h) * (∑ k, cs k * trc (ρs k) (h * g)) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have := congrArg (fun x => cs k * x) (hk k)
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun h _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib, e2, sub_zero]
    simp only [Finsupp.sum, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [trc, map_mul, Units.val_mul]
  rw [htr]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun h _ => ?_
  rw [norm_mul]
  calc ‖zOm l (G h)‖ * ‖trc r (h * g) - ∑ k, cs k * trc (ρs k) (h * g)‖
      ≤ 1 * ((l : ℝ)⁻¹) ^ (N + c) :=
        mul_le_mul (GlobalTheory.TraceConjugationCover.norm_zOm_le _) (happ (h * g)) (norm_nonneg _) zero_le_one
    _ = ((l : ℝ)⁻¹) ^ (N + c) := one_mul _

end GlobalTheory.CovKer
