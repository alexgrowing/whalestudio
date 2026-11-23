import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMap
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGrowthExponent

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

open CoefLow in

theorem values_eq_coef : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  intro D θ V τ hθ hHC hCW H _ _ σ lam ε P T _ hDS hP h hT v x
  haveI : CompleteSpace H := hDS.1
  have hstd := std_of_isDS hHC hDS
  have hσ := hstd.1
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSum.GKCoef.exists_growth_exponent θ V τ hθ hHC H σ lam ε P T hDS hP h hT x
  let F : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ → Mx V.rank → ℂ := fun w y => T w (x * atTau θ V τ (P⁻¹ * y * P))
  let f : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun w => mkBd (fun i => F w i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hN w
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [F, add_div]
      map_smul' := fun c v => by ext i; simp [F, mul_div_assoc] }
  obtain ⟨T₀, hT₀'⟩ := LinearMap.exists_extend f
  have hT₀ : ∀ (w : H) (hw : IsKFin ε σ w) (i : Unit × UJset ε),
      T₀ w i = F ⟨w, mem_kFin_iff.2 hw⟩ i.2.1 / wt N i.2.1 := fun w hw i => by
    have : T₀ w = f ⟨w, mem_kFin_iff.2 hw⟩ := LinearMap.congr_fun hT₀' ⟨w, mem_kFin_iff.2 hw⟩
    rw [this]; rfl
  have key : ∀ (w : H) (hw : IsKFin ε σ w), ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε,
      rt ε Unit N y (T₀ w) i = F ⟨w, mem_kFin_iff.2 hw⟩ (i.2.1 * y) / wt N i.2.1 := by
    intro w hw y hy i
    rw [rt_apply hy, hT₀ w hw]
    have := wt_ne N (i.2.1 * y)
    field_simp

  have hder : ∀ (w : H) (hw : IsKFin ε σ w) {X : Mx V.rank} (hX : X ∈ lieSet ε) {g : Mx V.rank} (hg : g ∈ UJset ε)
      (s : ℝ), HasDerivAt (fun t : ℝ => F ⟨w, mem_kFin_iff.2 hw⟩ (g * NormedSpace.exp (t • X)))
        (F ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ (g * NormedSpace.exp (s • X))) s := by
    intro w hw X hX g hg s
    have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
    have h1 := hasDerivAt_map hθ hP h hT ⟨w, mem_kFin_iff.2 hw⟩
      ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ hX (hstd.2.2.1 w hw) rfl x hs
    have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
    refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
    show F _ _ = F _ _
    simp only [F]
    rw [mul_assoc g (NormedSpace.exp (s • X)), ← exp_add_smul, add_sub_cancel]
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := GlobalTheory.TypeSum.casselmanWallach_banach hCW V.rank ε H σ hstd _ _
    (modRep_rt ε Unit N) T₀
    (fun k hk w hw => by
      ext i
      rw [key w hw k (K_le_UJ hk), hT₀ _ (isKFin_translate hw hk)]
      congr 1
      exact map_K hθ hP h hT hk _ _ rfl x i.2.2)
    (fun X hX w hw => by
      have hw1 := isKFin_dRep _ ε H σ hstd w hw X hX
      have hw2 := isKFin_dRep _ ε H σ hstd _ hw1 X hX
      obtain ⟨C2, hC2⟩ := hN ⟨_, mem_kFin_iff.2 hw2⟩
      obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
        ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
      refine hasDerivAt_of_sq (K := |C2| * |B|) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X w)) i = t • T₀ (dRep σ X w) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key w hw _ (exp_mem_UJ hX _),
        key w hw _ (exp_mem_UJ hX _), hT₀ _ hw1, zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
      have tb := taylor_two (hder w hw hX i.2.2) (hder _ hw1 hX i.2.2) (K := |C2| * |B| * wt N i.2.1)
        (fun s hs => by
          refine (hC2 _ (mul_mem_UJ i.2.2 (exp_mem_UJ hX s))).trans ?_
          have w1 := wt_mul_le N i.2.1 (NormedSpace.exp (s • X))
          have w2 : wt N (NormedSpace.exp (s • X)) ≤ |B| := (hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)
          have w3 := wt_pos N i.2.1
          have w4 := wt_pos N (i.2.1 * NormedSpace.exp (s • X))
          change C2 * wt N _ ≤ _
          calc C2 * wt N (i.2.1 * NormedSpace.exp (s • X)) ≤ |C2| * (wt N i.2.1 * |B|) :=
                mul_le_mul (le_abs_self _) (w1.trans (mul_le_mul_of_nonneg_left w2 w3.le)) w4.le (abs_nonneg _)
            _ = _ := by ring) ht
      simp only [zero_smul, NormedSpace.exp_zero, mul_one] at tb
      calc _ ≤ |C2| * |B| * wt N i.2.1 * t ^ 2 := tb
        _ = _ := by ring)
  let ℓ : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx V.rank) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun a b => by simp [mul_add]
      map_smul' := fun c a => by simp; ring }
  have hvK : IsKFin ε σ (v : H) := mem_kFin_iff.1 v.2
  refine ⟨ℓ, ⟨S, wt N (1 : Mx V.rank) * |C|, hS, fun w hw => ?_⟩, hstd.2.2.1 _ hvK, fun y hy => ?_⟩
  · change ‖(wt N (1 : Mx V.rank) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  · change _ = (wt N (1 : Mx V.rank) : ℂ) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
    rw [hT2 y hy _ (hstd.2.2.1 _ hvK), hT1 _ hvK, key _ hvK y hy]
    have := wt_ne N (1 : Mx V.rank)
    simp only [one_mul, F]
    field_simp

end GlobalTheory.TypeSum.GKCoef

end
