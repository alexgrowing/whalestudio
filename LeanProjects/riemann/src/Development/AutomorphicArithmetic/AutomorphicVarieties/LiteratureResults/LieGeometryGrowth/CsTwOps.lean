import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_contDiffOn {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F} (hw : ContDiffOn ℝ ∞ w Y) :
    ContDiffOn ℝ ∞ (tp A B w) Y := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  refine altSmooth _ _ _ q _ z fun v => ?_
  have h1 : ContDiffAt ℝ ∞ (fun y : V => w (A y)) z :=
    (hw.contDiffAt (hY.mem_nhds (hA z hz))).comp z A.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun y : V => w (A y) fun i => A (v i)) z :=
    (ContinuousAlternatingMap.apply ℝ V F (fun i => A (v i))).contDiff.contDiffAt.comp z h1
  exact B.contDiff.contDiffAt.comp z h2

private theorem twOps_abs {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] {Y : Set V} (hY : IsOpen Y) (A A' : V →L[ℝ] V) (B : F →L[ℝ] F)
    (hA : ∀ p ∈ Y, A p ∈ Y) (hA' : ∀ p ∈ Y, A' p ∈ Y) (h1 : ∀ p, A (A' p) = p) (h2 : ∀ p, A' (A p) = p)
    {W : V → V} (hW : IsField Y W) :
    IsField Y (fun p => A' (W (A p))) ∧ (∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p))) ∧
    ∀ q : ℕ, (∀ w : V → V [⋀^Fin q]→L[ℝ] F, ∀ p ∈ Y,
        tp A B (pb (flow W 1) w) p = pb (flow (fun p => A' (W (A p))) 1) (tp A B w) p) ∧
      ∀ w : V → V [⋀^Fin (q + 1)]→L[ℝ] F, ContDiffOn ℝ ∞ w Y → ∀ p ∈ Y,
        tp A B (hom W w) p = hom (fun p => A' (W (A p))) (tp A B w) p := by
  have hf : ∀ t p, flow (fun p => A' (W (A p))) t p = A' (flow W t (A p)) := fun t p => by
    simp only [flow, map_add, map_smul, h2]
  have hZ : IsField Y (fun p => A' (W (A p))) :=
    ⟨A'.contDiff.comp_contDiffOn (hW.1.comp A.contDiff.contDiffOn hA), fun p hp t ht => by
      rw [hf]; exact hA' _ (hW.2 _ (hA p hp) t ht)⟩
  refine ⟨hZ, hf, fun q => ?_⟩
  have nat := pbNat V F Y hY A' B W _ hW hZ hA' (fun p _ => by simp only [h1]) q
  have rel : ∀ (n : ℕ) (w : V → V [⋀^Fin n]→L[ℝ] F), ∀ p ∈ Y, ∀ v : Fin n → V,
      tp A B w (A' p) (fun i => A' (v i)) = B (w p v) := fun n w p _ v => by
    simp only [tp_apply, h1]
  refine ⟨fun w p hp => ?_, fun w hw p hp => ?_⟩
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := nat.1 _ _ (rel q w) 1 ⟨zero_le_one, le_rfl⟩ _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm
  · refine ContinuousAlternatingMap.ext fun v => ?_
    have := (nat.2 _ _ (rel (q + 1) w)).2 hw (tp_contDiffOn hY A B hA hw) _ (hA p hp) (fun i => A (v i))
    simp only [h2] at this
    exact this.symm

theorem UpperTheory.V.Lit.Geo.Cs.twOps :
    UpperTheory.V.Lit.Geo.Cs.TwOps := by
  intro E _ _ _ a ho U Ξ W hW g x
  have h1 : ∀ p : HV E a, sand g (sand g⁻¹ p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h2 : ∀ p : HV E a, sand g⁻¹ (sand g p) = p := fun p => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  obtain ⟨k1, k2, k3⟩ := twOps_abs ho (sand g) (sand g⁻¹) (mulVecL (Ξ.mat g⁻¹)) (fun p hp => sand_mem_cone g hp)
    (fun p hp => sand_mem_cone g⁻¹ hp) h1 h2 (hW.field (QuotientGroup.mk x))
  refine ⟨k1, k2, fun q => ?_⟩
  have app := omApply _ _ _ _ (geo ho U Ξ) W hW q
  refine ⟨fun w => ⟨tp_contDiffOn ho _ _ (fun p hp => sand_mem_cone g hp) (w.2 _).1, fun p hp => ?_⟩, fun w p hp => ?_⟩
  · refine Eq.trans ?_ ((k3 q).1 (w.1 _) p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.1 w _ _ (sand_mem_cone g hp)]
  · refine Eq.trans ?_ ((k3 q).2 (w.1 _) (w.2 _).1 p hp)
    refine ContinuousAlternatingMap.ext fun v => ?_
    rw [Tw, tp_apply, tp_apply, app.2 w _ _ (sand_mem_cone g hp)]
