import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSym

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X : Herm E a) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1), by
        have hX : star X.1 = X.1 := X.2
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) = X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1
        rw [star_add, star_mul, star_mul, hX, hv, add_comm]⟩
      map_add' := fun p p' => Subtype.ext (by
        change X.1 * (Matrix.of p.1 + Matrix.of p'.1) + (Matrix.of p.1 + Matrix.of p'.1) * X.1 =
          (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1) + (X.1 * Matrix.of p'.1 + Matrix.of p'.1 * X.1)
        rw [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change X.1 * (c • Matrix.of p.1) + (c • Matrix.of p.1) * X.1 = c • (X.1 * Matrix.of p.1 + Matrix.of p.1 * X.1)
        rw [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem jor_one (X : Herm E a) : jor X (hOne E a) = (2 : ℝ) • hv X := Subtype.ext (by
  change X.1 * 1 + 1 * X.1 = (2 : ℝ) • X.1
  rw [mul_one, one_mul, two_smul])

private theorem jor_comm (X Y : Herm E a) : jor X (hv Y) = jor Y (hv X) := Subtype.ext (by
  change X.1 * Y.1 + Y.1 * X.1 = Y.1 * X.1 + X.1 * Y.1
  rw [add_comm])

private theorem exists_curve (X : Herm E a) : ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧
    HasDerivAt (fun t => toL (c t).val) (toL X.1) 0 ∧
    ∀ v : HV E a, HasDerivAt (fun t => sand (c t) v) (jor X v) 0 := by
  classical
  have hX : star X.1 = X.1 := X.2
  have hu : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1) := by
    have hc : Continuous fun t : ℝ => (1 + t • X.1).det :=
      (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
    have h : ∀ᶠ t : ℝ in nhds 0, IsUnit (1 + t • X.1).det :=
      hc.continuousAt.eventually (Units.isOpen.mem_nhds (by simp))
    exact h.mono fun t ht => (Matrix.isUnit_iff_isUnit_det _).2 ht
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => if h : IsUnit (1 + t • X.1) then h.unit else 1
  have hc : ∀ᶠ t : ℝ in nhds 0, (c t).val = 1 + t • X.1 :=
    hu.mono fun t ht => by simp only [c, dif_pos ht, IsUnit.unit_spec]
  refine ⟨c, Units.ext (by simpa using hc.self_of_nhds), ?_, fun v => ?_⟩
  · have h := (((hasDerivAt_id (0 : ℝ)).smul_const (toL X.1)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))))
    rw [one_smul] at h
    exact h.congr_of_eventuallyEq (hc.mono fun t ht => by
      beta_reduce
      rw [ht]; rfl)
  · let B : HV E a := ⟨toL (X.1 * Matrix.of v.1 * star X.1), IsSelfAdjoint.conjugate v.2 X.1⟩
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const (jor X v)).const_add v).add
      (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).smul_const B)
    simp only [id, mul_zero, zero_mul, add_zero, zero_smul, one_smul] at h
    refine h.congr_of_eventuallyEq (hc.mono fun t ht => Subtype.ext ?_)
    change (c t).val * Matrix.of v.1 * star (c t).val =
      Matrix.of v.1 + t • (X.1 * Matrix.of v.1 + Matrix.of v.1 * X.1) + (t * t) • (X.1 * Matrix.of v.1 * star X.1)
    rw [ht, star_add, star_one, star_smul, star_trivial t, hX]
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel

theorem corrD : CorrD := by
  intro E _ _ _ a ho U Ξ q α w h g x X
  choose c hc0 hc1 hc2 using fun i => exists_curve (X i)
  have hp : sand g (hOne E a) ∈ (geo ho U Ξ).Y := ⟨g, rfl⟩
  have hinv : ∀ v : HV E a, sand g⁻¹ (sand g v) = v := fun v => by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  let L : Fin (q + 1) → HV E a →L[ℝ] HV E a := fun i => (sand g).comp ((jor (X i)).comp (sand g⁻¹))
  have hL : ∀ i v, L i (sand g v) = sand g (jor (X i) v) := fun i v => by
    simp only [L, ContinuousLinearMap.comp_apply, hinv]
  have hL1 : ∀ i, L i (sand g (hOne E a)) = (2 : ℝ) • sand g (hv (X i)) := fun i => by
    rw [hL, jor_one, map_smul]
  have hL2 : ∀ i j, L j (L i (sand g (hOne E a))) = (2 : ℝ) • sand g (jor (X i) (hv (X j))) := fun i j => by
    rw [hL1, map_smul, hL, jor_comm]
  have hd : ∀ i v, HasDerivAt (fun t => sand (g * c i t) v) (sand g (jor (X i) v)) 0 := fun i v => by
    have h1 := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hc2 i v)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [map_mul]; rfl
  have key := altSym (HV E a) (Fin Ξ.d → ℂ) q (w.1 (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) L
    (fun i t => sand (g * c i t) (hOne E a)) (fun i j t => (2 : ℝ) • sand (g * c i t) (hv (X j)))
    (fun i => Ξ.mat g *ᵥ ev (smLie Ξ (toL (X i).1) (α (i.removeNth X))) (infGL E a g * finGL E a x))
    (Geo.differentiableAt_Om w _ hp)
    (fun i j => by rw [hL2, hL2, jor_comm])
    (fun i => ⟨by rw [hc0, mul_one], by rw [hL]; exact hd i _⟩)
    (fun i j => ⟨by rw [hc0, mul_one, hL1], by rw [hL2]; exact (hd i _).const_smul (2 : ℝ)⟩)
    (fun i => by
      refine (evDeriv E a Ξ (α (i.removeNth X)) g x (c i) _ (hc0 i) (hc1 i)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => ?_)
      exact h (g * c i t) x (i.removeNth X))
  rw [Geo.dOm_apply _ w _ hp]
  simp only [hL1] at key
  rw [key, dCo_apply, map_sum, Finset.sum_apply, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, Matrix.mulVec_smul]

end UpperTheory.V.Lit.Dr
