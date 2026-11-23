import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsSecOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsChartSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDer

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem hv_coord (E : Type) [Field E] [NumberField E] (a : ℕ) :
    ∃ L : Fin a × Fin a × InfinitePlace E → ℂ →L[ℝ] HV E a,
      ∀ v : HV E a, v = ∑ n ∈ Finset.univ, L n (v.1 n.1 n.2.1 n.2.2) := by
  classical
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  refine ⟨fun n => LinearMap.toContinuousLinearMap (P ∘ₗ LinearMap.single ℝ (fun _ => Fin a → Cinf E) n.1 ∘ₗ
    LinearMap.single ℝ (fun _ => Cinf E) n.2.1 ∘ₗ LinearMap.single ℝ (fun _ => ℂ) n.2.2), fun v => ?_⟩
  have h1 : P v.1 = v := LinearMap.congr_fun hP v
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  rw [← map_sum]
  refine h1.symm.trans (congrArg P ?_)
  simp only [Fintype.sum_prod_type, ← map_sum]
  simp only [LinearMap.coe_single, Finset.univ_sum_single]

theorem UpperTheory.V.Lit.Geo.Cs.zwSz :
    ZwSz := by
  intro E _ _ _ a U Y C hY W hW k
  obtain ⟨B, -, hB⟩ := fieldDer E a U Y C hY
  obtain ⟨τ, h1, hτ, -, hs, -, he⟩ := secOne E a
  obtain ⟨L, hL⟩ := hv_coord E a
  choose φ hφ hb using hY.sm
  have e1 : toL (τ (hOne E a)).val = oneL E a := by rw [h1]; rfl
  have hc : ∀ i j w, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Sz k (chart (φ i j w).1 g) (oneL E a) (c * 1) := fun i j w => by
    refine chartSz E a k (fun _ => 1) (fun _ => zero_le_one) (φ i j w) fun l => ?_
    rcases l with _ | ⟨X, l⟩
    · refine ⟨B, fun g => ?_⟩
      rw [mul_one]
      change ‖(φ i j w).1 g‖ ≤ B
      rw [hφ]
      refine le_trans ?_ (hB g).1
      exact ((norm_le_pi_norm (toL (Y g).1 i j) w).trans (norm_le_pi_norm (toL (Y g).1 i) j)).trans
        (norm_le_pi_norm (toL (Y g).1) i)
    · obtain ⟨c, hc⟩ := hb i j w X l
      exact ⟨c, fun g => by rw [mul_one]; exact hc g⟩
  choose c _ hc using hc
  obtain ⟨b₁, hb₁⟩ := exists_sz k (fun p => toL (τ p).val) (hOne E a)
  obtain ⟨b₂, hb₂⟩ := exists_sz k (fun p => sand (τ p)) (hOne E a)
  obtain ⟨D, -, hD⟩ := compSz (HV E a) (Lie E a) ℂ k b₁
  refine ⟨2 ^ k * b₂ * ∑ n ∈ Finset.univ, ‖L n‖ * (D * (c n.1 n.2.1 n.2.2 * 1)), fun g x => ?_⟩
  have s0 : ∀ i j w, ContDiffAt ℝ ∞ (chart (φ i j w).1 (pt g x)) (toL (τ (hOne E a)).val) := fun i j w =>
    contDiffAt_chart (φ i j w).2 _ (val_mem_invSet _)
  have s1 : ∀ i j w, ContDiffAt ℝ ∞ (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) := fun i j w =>
    ContDiffAt.comp (g := chart (φ i j w).1 (pt g x)) (f := fun p => toL (τ p).val) (hOne E a) (s0 i j w) hτ
  have z1 : ∀ i j w, Sz k (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) (D * (c i j w * 1)) :=
    fun i j w => hD _ (fun p => toL (τ p).val) _ _ hτ (s0 i j w) (fun m _ hm => hb₁ m hm) (by rw [e1]; exact hc i j w _)
  have s2 : ∀ n : Fin a × Fin a × InfinitePlace E,
      ContDiffAt ℝ ∞ (fun p => L n (chart (φ n.1 n.2.1 n.2.2).1 (pt g x) (toL (τ p).val))) (hOne E a) := fun n =>
    (L n).contDiff.contDiffAt.comp (hOne E a) (s1 _ _ _)
  have z2 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).2.2 _ Finset.univ _ _ (fun n _ => s2 n)
    (fun n _ => (appSz (HV E a) ℂ (HV E a) k (hOne E a)).2.1 (L n) _ _ (s1 n.1 n.2.1 n.2.2) (z1 _ _ _))
  have z3 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).1 _ _ _ _ hs (ContDiffAt.sum fun n _ => s2 n) hb₂ z2
  refine z3.congr (he.mono fun p hp => ?_)
  have e2 := hW (g * τ p) x
  have e3 : sand (g * τ p) (hOne E a) = sand g p := by rw [map_mul, ContinuousLinearMap.mul_apply, hp]
  rw [e3] at e2
  simp only [chart_val, hφ, Zw, e2, ← pt_mul]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  exact congrArg _ (hL (hv (Y (pt (g * τ p) x)))).symm
