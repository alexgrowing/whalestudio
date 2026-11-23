import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem wseed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  intro l _ K bk τ hτ d ρ hρ s y hy _hcau z hz
  beta_reduce at hy ⊢
  obtain ⟨hρ0, hρ1⟩ := bk.ρ₀_mem_Ioo_zero_one
  have hX : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  set j₀ : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hX with hj₀
  have hj₀d : IsDiscMap bk.ev j₀ := isDiscMap_map bk.ev hX
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨cD, hc_to, hc_mul, hc_norm, -⟩ := GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j₀ hj₀d
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB (2 * s.N * d)
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hr

  set V : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀) := s.W'.det • adjugate s.W with hV
  have hVW : V * s.W = bk.iA (τ ^ (2 * s.N * d)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have hd : s.W.det * s.W'.det = bk.iA (τ ^ (2 * s.N * d)) := by
      rw [← det_mul, s.W_mul, det_smul, det_one, mul_one, Fintype.card_fin, map_pow]
      ring
    rw [hV, smul_mul, adjugate_mul, smul_smul, mul_comm, hd]

  let Φ : bk.DA bk.ρ₀ → bk.DS bk.ρ₀ := fun w => ∑ i ∈ f.support, toDisc l (X : bk.S) bk.ρ₀ (f i) * cD i w
  have key : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      (l : bk.DS bk.ρ₀) ^ r * x a = Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    have hsm : ∀ (c : bk.DA bk.ρ₀) (v : Fin d → bk.DA bk.ρ₀), (c • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))) *ᵥ v = c • v := by
      intro c v; ext b; simp [mulVec, dotProduct, Matrix.one_apply]
    rw [mulVec_mulVec, hVW, hsm]
    have h1 : ∀ i, cD i ((bk.iA (τ ^ (2 * s.N * d)) • fun b => j₀ (x b)) a) =
        x a * toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hc_mul, hc_to]
    simp only [Φ, h1]
    have h2 := congrArg (toDisc l (X : bk.S) bk.ρ₀) hf
    rw [Finsupp.sum, map_sum, map_pow, map_natCast] at h2
    rw [← h2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, map_mul]; ring
  obtain ⟨u, hu⟩ : IsUnit ((l : bk.DS bk.ρ₀) ^ r) := (isUnit_l_disc l (X : bk.S) bk.ρ₀).pow r
  have hsol : ∀ (x : Fin d → bk.DS bk.ρ₀) (a : Fin d),
      x a = ↑u⁻¹ * Φ ((V *ᵥ (s.W *ᵥ fun b => j₀ (x b))) a) := by
    intro x a
    rw [← key, ← hu, Units.inv_mul_cancel_left]

  have hcont : ∀ {F : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀}, IsDiscMap bk.ev F → Continuous F := fun hF =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hF.norm_le x).trans (one_mul _).ge
  have hcDc : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun x => (hc_norm i x).trans (one_mul _).ge
  let G : (Fin d → bk.DA bk.ρ₀) → (Fin d → bk.DA bk.ρ₀) := fun v =>
    s.W *ᵥ fun a => j₀ (↑u⁻¹ * Φ ((V *ᵥ v) a))
  have hGc : Continuous G := by
    refine continuous_const.matrix_mulVec (continuous_pi fun a => (hcont hj₀d).comp (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      ((hcDc i).comp ((continuous_apply a).comp (continuous_const.matrix_mulVec continuous_id)))
  have hGy : ∀ n, G (fun a => bk.iA (y n a)) = fun a => bk.iA (y n a) := by
    intro n
    obtain ⟨x, hx⟩ := hy n
    have hxe := hx j₀ hj₀d
    have h3 : G (s.W *ᵥ fun b => j₀ (x b)) = s.W *ᵥ fun b => j₀ (x b) := by
      dsimp only [G]; congr 1; funext a; rw [← hsol x a]
    rwa [hxe] at h3

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n => fun a => bk.iA (y n a)) Filter.atTop (nhds fun a => bk.iA (z a)) := by
    rw [tendsto_pi_nhds]; intro a
    have h0 : Filter.Tendsto (fun n => bk.iA (z a - y n a)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl1))
      obtain ⟨w, hw⟩ := hz n a
      rw [hw]; exact norm_toDisc_natPow_mul_le _ _ n w
    have h4 := (tendsto_const_nhds (x := bk.iA (z a))).sub h0
    simpa only [sub_zero, map_sub, sub_sub_cancel] using h4
  have hfix : G (fun a => bk.iA (z a)) = fun a => bk.iA (z a) :=
    (isClosed_eq hGc continuous_id).mem_of_tendsto ht (Filter.Eventually.of_forall hGy)
  refine ⟨fun a => ↑u⁻¹ * Φ ((V *ᵥ fun b => bk.iA (z b)) a), fun j hj => ?_⟩
  rw [hj.unique hj₀d]
  exact hfix

end GlobalTheory.BKLim
