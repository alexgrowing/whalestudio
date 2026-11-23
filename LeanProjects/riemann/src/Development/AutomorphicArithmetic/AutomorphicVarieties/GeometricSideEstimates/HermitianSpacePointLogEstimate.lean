import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideLowerBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.NsmulOrbitBoundedOfCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem pt_ne_zero {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a)
    (v : Fin a → E) (hv : v ≠ 0) : pt g v ≠ 0 := by
  intro h
  apply hv
  have h1 : vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val = 0 := h
  have h2 : vInf v = 0 := by
    have := congrArg (fun x => x ᵥ* ((GeneralLinearGroup.map (pInf E) g)⁻¹).val) h1
    simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this
  funext i
  have h3 : ((pInf E : Ad E →+* Cinf E).comp (algebraMap E (Ad E))) (v i) = 0 := congrFun h2 i
  exact (map_eq_zero_iff _ (RingHom.injective _)).1 h3

private theorem log_bound {H q T C : ℝ} {N : ℕ} (hH : 1 ≤ H) (hT : 1 ≤ T) (hq : 0 < q)
    (h1 : H * (q ^ 2) ^ N ≤ C) (h2 : Real.exp (-Real.pi) ≤ q * T) :
    Real.log H ≤ (|Real.log C| + 2 * N * Real.pi + 2 * N) * (1 + Real.log T) := by
  have hH0 : 0 < H := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have a1 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hH0.ne' (by positivity), Real.log_pow, Real.log_pow] at a1
  have a2 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp, Real.log_mul hq.ne' hT0.ne'] at a2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have a3 := mul_le_mul_of_nonneg_left a2 hN
  have a4 := le_abs_self (Real.log C)
  have a5 := mul_nonneg (abs_nonneg (Real.log C)) hl
  have a6 := mul_nonneg (mul_nonneg hN Real.pi_pos.le) hl
  push_cast at a1
  nlinarith

theorem UpperTheory.hermitian_space_point_log_estimate :
    LeFn := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC⟩ := UpperTheory.nsmul_orbit_bounded_of_compact E a ha L hL
  obtain ⟨M, hM⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  have hT := (UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1
  refine ⟨|Real.log C| + 2 * N * Real.pi + 2 * N, fun g => ?_⟩
  obtain ⟨v, hv, hv0, hb⟩ := hC g
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    (euc.toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ x : lat L g, ‖φ x‖ ^ 2 = qf (pt (rt g) x.1) := fun x => norm_euc_sq _
  have hs : Summable fun x => Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    have := ((hM g).2 1 1 one_pos le_rfl).1
    simpa only [hφ, one_mul] using this
  have hne : φ ⟨v, hv⟩ ≠ 0 := fun h => pt_ne_zero (rt g) v hv0 (euc.injective (h.trans (map_zero euc).symm))
  have hlow := UpperTheory.geometric_side_lower_bound (lat L g) _ φ hs ⟨v, hv⟩ hne
  have hTh : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) = Th L g := by
    simp only [hφ]
    rfl
  rw [hTh] at hlow
  refine log_bound ((UpperTheory.V.Lit.Geo.qhtFacts E a).1 g) (hT g).1 (norm_pos_iff.2 hne) ?_ hlow
  rw [hφ]
  exact hb
