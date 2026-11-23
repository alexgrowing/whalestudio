import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem exists_eval_points {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (N : ℕ) (x : Fin N → X) (f : Fin N → X → ℂ), (∀ i, f i ∈ W) ∧
      ∀ w ∈ W, ∀ y, w y = ∑ i, w (x i) * f i y := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hch : ∀ φ : s, ∃ x, ev x = φ.1 := fun φ => hs φ.2
  choose pt hpt using hch
  let e := s.equivFin
  let x : Fin s.card → X := fun i => pt (e.symm i)
  let T : W →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (x i)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hle : Submodule.span ℂ (s : Set (Module.Dual ℂ W)) ≤ LinearMap.ker (Module.Dual.eval ℂ W w) := by
      rw [Submodule.span_le]
      intro φ hφ
      have h1 : T w (e ⟨φ, hφ⟩) = 0 := by rw [hw]; rfl
      have h2 : ev (x (e ⟨φ, hφ⟩)) w = 0 := h1
      have h3 : ev (x (e ⟨φ, hφ⟩)) = φ := by
        show ev (pt (e.symm (e ⟨φ, hφ⟩))) = φ
        rw [Equiv.symm_apply_apply, hpt]
      rw [h3] at h2
      exact h2
    refine Subtype.ext (funext fun y => ?_)
    have hy : ev y ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ W)) :=
      hspan ▸ Submodule.subset_span ⟨y, rfl⟩
    exact hle hy
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨s.card, x, fun i => (L (Pi.single i 1)).1, fun i => (L _).2, ?_⟩
  intro w hw y
  have h1 : L (T ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hL _
  have h2 : T ⟨w, hw⟩ = ∑ i, w (x i) • (Pi.single i (1 : ℂ) : Fin s.card → ℂ) := by
    ext j
    simp [T, ev, Finset.sum_apply, Pi.single_apply]
  rw [h2, map_sum] at h1
  have h3 := congrArg (fun v : W => v.1 y) h1
  simp only [map_smul] at h3
  simpa [Submodule.coe_sum, Finset.sum_apply] using h3.symm

theorem rank_one_majorant_of_parts : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  intro hCont hFin hOrb hIwa D n ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl hl0 Φ hΦ C hC
  have hcart : ∀ τ, IsCartanInv (gramAt D (V1 D) τ)
      ((fun _ => 1 : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) τ) :=
    fun τ => GlobalTheory.AdForm.VacStd.cartan_of_gram (GlobalTheory.AdForm.VacStd.gram_of_eq _ _ 1 rfl) τ
  obtain ⟨W, hWfd, hWle, hWK⟩ :=
    hFin D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl (fun _ => 1) hcart Φ hΦ
  haveI := hWfd
  obtain ⟨N, x, f, hfW, hrep⟩ := exists_eval_points W
  have hcont := hCont D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω Φ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K D n, ‖(ω k Φ).1 (x i)‖ ≤ B := by
    intro i
    have hc : Continuous fun k : G D n => (ω k Φ).1 (x i) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB⟩ := HeightExists.isCompact_K.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  obtain ⟨A₁, A₂, R, hA₁, hA₂, hiwa⟩ := hIwa D n C hC
  have hM := fun i => hOrb D n θ hθ l hl0 (f i) (hWle (hfW i)) A₁ A₂ hA₁ hA₂
  choose M hMs hMpos hMle using hM
  have hc0 : 0 ≤ (max R 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  refine ⟨(((max R 0) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hMs i)), ?_⟩
  intro h hh y
  obtain ⟨m, t, k, a, b, hk, rfl, hm, ht, ha1, ha2, hR⟩ := hiwa h hh
  set c : ℝ := (max R 0) ^ ((1 : ℝ) / 2) with hc
  have e1 : ‖(ω (m * t * k) Φ).1 y‖ =
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) * ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.levi m a hm, hω.unip t b ht,
      norm_mul, norm_mul, norm_mul, hψ.2.1, norm_npow (hom_pos _ _)]
    have hre : (((V1 D).rank : ℂ) / 2).re = (1 : ℝ) / 2 := by
      show ((((1 : ℕ) : ℂ)) / 2).re = (1 : ℝ) / 2
      norm_num
    rw [hre, Circle.norm_coe, one_mul, one_mul]
  have e2 : ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ∑ i, B i * ‖M i y‖ := by
    rw [hrep _ (hWK k hk)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i k hk) (hMle i a ha1 ha2 y) (norm_nonneg _) (hB0 i)
  have e3 : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _) (hR.trans (le_max_left _ _)) (by norm_num)
  have e4 : ∀ i, M i y = ((‖M i y‖ : ℝ) : ℂ) := by
    intro i
    have h1 := hMpos i y
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [show M i y = (((M i y).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [h1.2])]
      simp [abs_of_nonneg h1.1]
    · simp [h1.2]
  have e5 : ‖((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y‖ = c * ∑ i, B i * ‖M i y‖ := by
    have h1 : ((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y =
        ((c * ∑ i, B i * ‖M i y‖ : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← e4 i]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (norm_nonneg _))
  rw [e1, e5]
  exact mul_le_mul e3 e2 (norm_nonneg _) hc0

end GlobalTheory.CompanionTheory.ThTot

end
