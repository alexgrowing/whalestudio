import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTpSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open scoped ContDiff

private theorem tp_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] V) (B : F →L[ℝ] F) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) (hw : ContDiffAt ℝ ∞ w (A p)) :
    ContDiffAt ℝ ∞ (Cs.tp A B w) p := by
  have h1 : ContDiffAt ℝ ∞ (fun x => w (A x)) p := hw.comp p A.contDiff.contDiffAt
  have h2 := (ContinuousAlternatingMap.compContinuousLinearMapCLM A :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F)).contDiff.contDiffAt.comp p h1
  exact (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V F F (Fin q) B).contDiff.contDiffAt.comp p h2

theorem UpperTheory.V.Lit.Geo.Cs.move :
    UpperTheory.V.Lit.Geo.Cs.Move := by
  intro E _ _ _ a ho U Ξ q k c
  obtain ⟨B, hB, hb⟩ := matBd E a Ξ c
  obtain ⟨D, hD, hd⟩ := Cs.tpSz (HV E a) (Fin Ξ.d → ℂ) q k B
  refine ⟨D, hD, fun w g x h b hh hs => ?_⟩
  obtain ⟨h1, -, h3⟩ := hb h hh.1 hh.2
  have e : sand h⁻¹ (sand h (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  rw [Cs.Tw_eq U Ξ w.1 g h x]
  refine hd _ _ _ _ b (ContinuousLinearMap.opNorm_le_bound _ hB h3)
    (ContinuousLinearMap.opNorm_le_bound _ hB fun y => by rw [mulVecL_apply]; exact h1 y) ?_ (by rw [e]; exact hs)
  rw [e]
  exact tp_smooth _ _ _ _ ((w.2 _).1.contDiffAt (ho.mem_nhds (sand_mem_cone _ hOne_mem_cone)))
