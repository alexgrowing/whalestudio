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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

open GlobalTheory.TypeSum.CoefLow GlobalTheory.LowTypeDetermined

namespace GlobalTheory.TypeSum.GrowthForm

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)} {N : ℕ} {T : H →ₗ[ℂ] (Mx n → ℂ)}

omit [CompleteSpace H] in
theorem deriv_at (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X)))
      (T (dRep σ X v) (g * NormedSpace.exp (s • X))) s := by
  have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
  have h1 := hd v hv X hX _ hs
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = T v _
  rw [mul_assoc, ← exp_add_smul, add_sub_cancel]

theorem taylor (h : Std ε σ)
    (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g)
    (hd : ∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0)
    {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    ∃ C, 0 ≤ C ∧ ∀ g ∈ UJset ε, ∀ t : ℝ, |t| ≤ 1 →
      ‖T v (g * NormedSpace.exp (t • X)) - T v g - t • T (dRep σ X v) g‖ ≤ C * wt N g * t ^ 2 := by
  have hv1 := isKFin_dRep n ε H σ h v hv X hX
  have hv2 := isKFin_dRep n ε H σ h _ hv1 X hX
  obtain ⟨C, hC⟩ := hb _ hv2
  obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
    ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
  refine ⟨|C| * |B|, by positivity, fun g hg t ht => ?_⟩
  have := taylor_two (deriv_at hd hv hX hg) (deriv_at hd hv1 hX hg)
    (K := |C| * |B| * wt N g) (fun s hs => by
      refine (hC _ (mul_mem_UJ hg (exp_mem_UJ hX s))).trans ?_
      refine (mul_le_mul_of_nonneg_right (le_abs_self C) (wt_pos _ _).le).trans ?_
      rw [mul_assoc, mul_comm |B|]
      refine mul_le_mul_of_nonneg_left ((wt_mul_le N g _).trans ?_) (abs_nonneg C)
      exact mul_le_mul_of_nonneg_left ((hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)) (wt_pos N g).le) ht
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one] using this

omit [CompleteSpace H] in
theorem exists_bdMap (hb : ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g) :
    ∃ T₀ : H →ₗ[ℂ] Bd (Unit × UJset ε), ∀ v, IsKFin ε σ v → ∀ i, T₀ v i = T v i.2.1 / wt N i.2.1 := by
  let f : kfin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun v => mkBd (fun i => T v i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hb v v.2
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [add_div]
      map_smul' := fun c v => by ext i; simp [mul_div_assoc] }
  obtain ⟨T₀, hT⟩ := LinearMap.exists_extend f
  refine ⟨T₀, fun v hv i => ?_⟩
  have : T₀ v = f ⟨v, hv⟩ := LinearMap.congr_fun hT ⟨v, hv⟩
  rw [this]
  rfl

theorem exists_form : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  intro hCW n ε H _ _ _ σ h N T hb hK hd
  change ∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * wt N g at hb
  obtain ⟨T₀, hT₀⟩ := exists_bdMap hb
  have key : ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, ∀ i, rt ε _ N y (T₀ v) i = T v (i.2.1 * y) / wt N i.2.1 := by
    intro v hv y hy i
    rw [rt_apply hy, hT₀ v hv]
    have := wt_ne N (i.2.1 * y)
    field_simp
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := casselmanWallach_banach hCW n ε H σ h _ _ (modRep_rt ε Unit N) T₀
    (fun k hk v hv => by
      ext i
      rw [key v hv k (K_le_UJ hk), hT₀ _ (isKFin_translate hv hk), hK v hv k hk _ i.2.2])
    (fun X hX v hv => by
      obtain ⟨C, hC, hb⟩ := taylor h hb hd hv hX
      refine hasDerivAt_of_sq (K := C) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X v)) i = t • T₀ (dRep σ X v) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key v hv _ (exp_mem_UJ hX _),
        key v hv _ (exp_mem_UJ hX _), hT₀ _ (isKFin_dRep n ε H σ h v hv X hX), zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _), mul_right_comm]
      exact hb _ i.2.2 t ht)
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx n) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun x y => by simp [mul_add]
      map_smul' := fun c x => by simp; ring }
  have hL : ∀ w, Sm ε σ w → ‖L w‖ ≤ wt N (1 : Mx n) * |C| * sobNorm σ S w := fun w hw => by
    change ‖(wt N (1 : Mx n) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  refine ⟨L, ⟨S, _, hS, hL⟩, fun v hv y hy => ?_⟩
  change _ = wt N (1 : Mx n) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
  rw [hT2 y hy v (h.2.2.1 v hv), hT1 v hv, key v hv y hy]
  have := wt_ne N (1 : Mx n)
  simp only [one_mul]
  field_simp

end GlobalTheory.TypeSum.GrowthForm

end
