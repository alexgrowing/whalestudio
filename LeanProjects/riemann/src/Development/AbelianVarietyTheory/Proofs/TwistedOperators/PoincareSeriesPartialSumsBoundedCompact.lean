import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModeratStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.PoinAut.partialSum_bdd : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  intro D θ hθ V S M Λ 𝔪 hΛ v hv _ c a Kc hK
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef
  set N := 2 * V.rank ^ 2 + 1 with hN
  obtain ⟨C₀, A₀, hI⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v (fun τ => (a τ : M.H τ)) N
    (fun τ => (hv τ).2 _ (a τ).2)
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn (GlobalTheory.Grow.continuous_height V).continuousOn
  set P : ℝ := ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg fun τ _ =>
    pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _
  have hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤ := fun y hy => by
    rw [congLev_top]; exact ⟨hy.1, hy.2.1⟩
  refine ⟨C * P * (max C₀ 0 * H ^ A₀), fun x hx s => ?_⟩
  have hterm : ∀ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
      ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ ≤
        C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by
    intro γ hγ
    unfold coef
    rw [if_pos (Finset.mem_filter.1 hγ).2]
    have := hCb (c * (γ : GA D V) * x) 1
    rwa [mul_one] at this
  have hx0 : 0 ≤ height V x := (height_pos V x).le
  have hxH : height V x ≤ H := by
    have := hH x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0] at this
  calc ∑ γ ∈ s, ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖
      = ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ := by
        refine (Finset.sum_filter_of_ne fun γ _ h => ?_).symm
        by_contra hn
        exact h (by unfold coef; rw [if_neg hn, norm_zero])
    _ ≤ ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := Finset.sum_le_sum hterm
    _ = C * P * ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C * P * (C₀ * height V x ^ A₀) :=
        mul_le_mul_of_nonneg_left (hI x _ fun γ hγ => hKtop _ (Finset.mem_filter.1 hγ).2) (mul_nonneg hC hP)
    _ ≤ C * P * (max C₀ 0 * H ^ A₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hP)
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hx0 hxH _) (pow_nonneg hx0 _) (le_max_right _ _)
