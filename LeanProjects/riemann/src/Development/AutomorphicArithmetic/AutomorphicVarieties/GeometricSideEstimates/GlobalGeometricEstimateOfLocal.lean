import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
open UpperTheory.V.Lit.Geo
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

private theorem key {E : Type} [Field E] [NumberField E] {a : ℕ} (g : GA E a) {c x : E} (hc : c ≠ 0) (hx : x ≠ 0)
    (y : Fin a → Ad E) (i : Fin a) (hy : algebraMap E (Ad E) x = ∑ j, y j * (g⁻¹).val j i)
    (hf : ∀ j p, ‖(algebraMap E (Ad E) c * y j).2 p‖ ≤ 1) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ j w, ‖(y j).1 w‖ ≤ r) :
    1 ≤ (∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a * r) ^ w.mult) * AutomorphicForm.height (K := E) g := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  have e : algebraMap E (Ad E) (c * x) = ∑ j, (algebraMap E (Ad E) c * y j) * (g⁻¹).val j i := by
    rw [map_mul, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  rw [← prod_norm_mul_finprod_norm hcx, AutomorphicForm.height, ← mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by have := locHeight_pos (infAt w g); positivity)
  · refine Finset.prod_le_prod (fun _ _ => pow_nonneg (norm_nonneg _) _) fun w _ => ?_
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h1 : ((c * x : E) : w.Completion) = ∑ j, ((c : w.Completion) * (y j).1 w) * ((infAt w g)⁻¹).val j i := by
      have := congrArg (infEval w) e
      rw [map_sum] at this
      refine Eq.trans this (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_mul, map_mul, ← infAt_inv]
      rfl
    rw [h1]
    calc _ ≤ ∑ _j : Fin a, ‖(c : w.Completion)‖ * r * locHeight (infAt w g) := by
          refine norm_sum_le_of_le _ fun j _ => ?_
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hr j w) (norm_nonneg _))
            (norm_inv_apply_le_locHeight _ j i) (norm_nonneg _) (by positivity)
      _ = _ := by simp; ring
  · refine finprod_le_finprod (Filter.eventually_cofinite.1 (eventually_norm_eq_one hcx)) (fun _ => norm_nonneg _)
      (finite_mulSupport_locHeight_finAt g) fun p => ?_
    have h1 : ((c * x : E) : p.adicCompletion E) =
        ∑ j, (algebraMap E (Ad E) c * y j).2 p * ((finAt p g)⁻¹).val j i := by
      have := congrArg (finEval p) e
      rw [map_sum] at this
      refine Eq.trans this (Finset.sum_congr rfl fun j _ => ?_)
      rw [map_mul, ← finAt_inv]
      rfl
    change ‖((c * x : E) : p.adicCompletion E)‖ ≤ locHeight (finAt p g)
    rw [h1]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (locHeight_pos _).le fun j _ => ?_
    rw [norm_mul]
    exact (mul_le_mul (hf j p) (norm_inv_apply_le_locHeight _ j i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem UpperTheory.global_geometric_estimate_of_local :
    LatMin := by
  intro E _ _ _ a _ L hL
  have hT : IsCompact (⋃ j : Fin a, (fun y : Fin a → Af E => y j) '' (L : Set (Fin a → Af E))) :=
    isCompact_iUnion fun j => hL.isCompact.image (continuous_apply j)
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hc : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  set c := algebraMap (𝓞 E) E d with hcdef
  set A : ℝ := ∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a) ^ 2 with hA
  refine ⟨max 1 A, 1, le_max_left _ _, fun g v hv hv0 => ?_⟩
  rw [pow_one]
  have hH := one_le_height (K := E) g
  have hq0 := qf_nonneg (pt g v)
  rcases le_total 1 (qf (pt g v)) with hq | hq
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hH) hq
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  set y : Fin a → Ad E := ratVec v ᵥ* g.val with hy
  have hyi : algebraMap E (Ad E) (v i) = ∑ j, y j * (g⁻¹).val j i := by
    have : y ᵥ* (g⁻¹).val = ratVec v := by
      rw [hy, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    exact (congrFun this i).symm
  have hF : ∀ j, (y j).2 = ptF g v j := fun j => by
    change pFin E (∑ k, ratVec v k * g.val k j) = ∑ k, vFin v k * pFin E (g.val k j)
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; rfl
  have hI : ∀ j, pInf E (y j) = pt g v j := fun j => by
    change pInf E (∑ k, ratVec v k * g.val k j) = ∑ k, vInf v k * pInf E (g.val k j)
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul]; rfl
  have hn : ∀ (x : Ad E) (w : InfinitePlace E), ‖pInf E x w‖ = ‖x.1 w‖ := fun x w =>
    (AddMonoidHomClass.isometry_iff_norm (InfinitePlace.Completion.extensionEmbedding w)).1
      (InfinitePlace.Completion.isometry_extensionEmbedding w) (x.1 w)
  have h := key g hc hi y i hyi (fun j p => by
      have h1 := hd (ptF g v j) (Set.mem_iUnion.2 ⟨j, ptF g v, hv, rfl⟩)
      rw [← hF] at h1
      exact norm_le_one_of_mem p (GroundTheory.Global.mem_integralFiniteAdeles.1 h1 p))
    (norm_nonneg (pt g v)) fun j w => by
      rw [← hn, hI]
      exact (norm_le_pi_norm (pt g v j) w).trans (norm_le_pi_norm _ j)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w => InfinitePlace.IsComplex.mult_eq_two (IsTotallyComplex.isComplex w)
  have hr := ((UpperTheory.geometric_side_quadraticForm_identity E a).2.2.2.2.2 (pt g v)).1
  have h2 : (∏ w : InfinitePlace E, (‖(c : w.Completion)‖ * a * ‖pt g v‖) ^ w.mult) ≤ max 1 A * qf (pt g v) := by
    simp only [hm, mul_pow _ ‖pt g v‖, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    refine mul_le_mul (le_max_right _ _) ?_ (by positivity) (by positivity)
    exact (pow_le_of_le_one (sq_nonneg _) (hr.trans hq) Fintype.card_ne_zero).trans hr
  calc 1 ≤ _ := h
    _ ≤ max 1 A * qf (pt g v) * AutomorphicForm.height (K := E) g := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring
