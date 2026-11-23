import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def pol0 (A B : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ⟨toL (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A), by
        have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
        change star (A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A) =
          A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A
        simp only [star_add, star_mul, star_star, hv, mul_assoc]
        exact add_comm _ _⟩
      map_add' := fun p p' => Subtype.ext (by
        change A * (Matrix.of p.1 + Matrix.of p'.1) * star B + B * (Matrix.of p.1 + Matrix.of p'.1) * star A =
          (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A) +
            (A * Matrix.of p'.1 * star B + B * Matrix.of p'.1 * star A)
        simp only [mul_add, add_mul]; abel)
      map_smul' := fun c p => Subtype.ext (by
        change A * (c • Matrix.of p.1) * star B + B * (c • Matrix.of p.1) * star A =
          c • (A * Matrix.of p.1 * star B + B * Matrix.of p.1 * star A)
        simp only [mul_smul_comm, smul_mul_assoc, smul_add]) }

private theorem polarization_val (A B : Matrix (Fin a) (Fin a) (Cinf E)) (v : HV E a) :
    Matrix.of (pol0 A B v).1 = A * Matrix.of v.1 * star B + B * Matrix.of v.1 * star A := rfl

private theorem hv_ext {v w : HV E a} (h : Matrix.of v.1 = Matrix.of w.1) : v = w := Subtype.ext h

private theorem polarization_comm (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 A B = pol0 B A :=
  ContinuousLinearMap.ext fun v => hv_ext (by rw [polarization_val, polarization_val, add_comm])

private theorem polarization_add (A A' B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (A + A') B = pol0 A B + pol0 A' B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = Matrix.of (pol0 A B v).1 + Matrix.of (pol0 A' B v).1
    simp only [polarization_val, star_add, mul_add, add_mul]; abel)

private theorem polarization_smul (c : ℝ) (A B : Matrix (Fin a) (Fin a) (Cinf E)) : pol0 (c • A) B = c • pol0 A B :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change _ = c • Matrix.of (pol0 A B v).1
    simp only [polarization_val, star_smul, star_trivial c, mul_smul_comm, smul_mul_assoc, smul_add])

variable (E a) in

private def pol : Lie E a →L[ℝ] Lie E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (fun A B : Lie E a => pol0 (Matrix.of A) (Matrix.of B)) (fun A A' B => polarization_add _ _ _)
      (fun c A B => polarization_smul c _ _)
      (fun A B B' => (polarization_comm _ _).trans ((polarization_add _ _ _).trans (congrArg₂ (· + ·) (polarization_comm _ _) (polarization_comm _ _))))
      (fun c A B => (polarization_comm _ _).trans ((polarization_smul c _ _).trans (congrArg (c • ·) (polarization_comm _ _)))))

private theorem pol_apply (A B : Lie E a) : pol E a A B = pol0 (Matrix.of A) (Matrix.of B) := rfl

private theorem pol_sand (g : GL (Fin a) (Cinf E)) :
    sand g = (2⁻¹ : ℝ) • pol E a (toL g.val) (toL g.val) :=
  ContinuousLinearMap.ext fun v => hv_ext (by
    change g.val * Matrix.of v.1 * star g.val =
      (2⁻¹ : ℝ) • (g.val * Matrix.of v.1 * star g.val + g.val * Matrix.of v.1 * star g.val)
    rw [← two_smul ℝ, smul_smul]; norm_num)

private theorem sand_der (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hX : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => sand (c t)) (pol E a X (toL 1)) 0 := by
  have h1 := (((pol E a).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hX).clm_apply hX).const_smul (2⁻¹ : ℝ)
  simp only [Function.comp, h0, Units.val_one] at h1
  have e : pol E a (toL 1) X = pol E a X (toL 1) := polarization_comm _ _
  rw [e, ← two_smul ℝ, smul_smul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, one_smul] at h1
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => pol_sand _)

private theorem pol_one (v : HV E a) : pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) (hOne E a) = v := by
  rw [map_smul]
  refine hv_ext ?_
  have hv : star (Matrix.of v.1) = Matrix.of v.1 := v.2
  change (2⁻¹ : ℝ) • (Matrix.of v.1 * 1 * star 1 + 1 * 1 * star (Matrix.of v.1)) = _
  rw [hv, star_one, mul_one, mul_one, one_mul, one_mul, ← two_smul ℝ, smul_smul]; norm_num

private theorem flow_der {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (h : DifferentiableAt ℝ W p) (t : ℝ) (v : V) : fderiv ℝ (flow W t) p v = v + t • fderiv ℝ W p v := by
  have h4 : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (h.hasFDerivAt.const_smul t)
  rw [h4.fderiv]
  rfl

theorem fieldBd : FieldBd := by
  intro E _ _ _ a U Y C hY W hW
  obtain ⟨B, hB, hD⟩ := fieldDer E a U Y C hY
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  set K : ℝ := ‖(pol E a).flip (toL 1)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨1 + (K * B + B), by positivity, fun g x t ht v => ?_⟩
  obtain ⟨c, h0, -, -, hX, -⟩ := oneParam E a ((2⁻¹ : ℝ) • v.1)
  obtain ⟨hb, hz⟩ := hD (infGL E a g * finGL E a x)
  obtain ⟨Z, hZ, hd⟩ := hz c _ h0 hX
  have hn : ‖(2⁻¹ : ℝ) • v.1‖ ≤ ‖v‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  have hs := sand_der c _ h0 hX
  set P := pol E a ((2⁻¹ : ℝ) • v.1) (toL 1) with hP
  set y := hv (Y (infGL E a g * finGL E a x)) with hy
  have hPn : ‖P‖ ≤ K * ‖v‖ :=
    (((pol E a).flip (toL 1)).le_opNorm _).trans (mul_le_mul_of_nonneg_left hn hK0)
  have hWd : DifferentiableAt ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) :=
    ((fieldSm E a U Y C hY W hW x).contDiffAt (ho.mem_nhds ⟨g, rfl⟩)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun r => sand g (sand (c r) (hOne E a))) (sand g v) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply (hasDerivAt_const (0 : ℝ) (hOne E a)))
    rwa [map_zero, add_zero, hP, pol_one] at h
  have h2 : HasDerivAt (fun r => W (x : GL (Fin a) (Af E) ⧸ U) (sand g (sand (c r) (hOne E a)))) (sand g (P y + Z)) 0 := by
    have h := (sand g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hs.clm_apply hd)
    simp only [h0, map_one, mul_one, ContinuousLinearMap.one_apply] at h
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have e : infGL E a (g * c r) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c r) := by
      rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
    have e2 := hW (g * c r) x
    rw [e, map_mul] at e2
    exact e2
  have h3 : fderiv ℝ (W (x : GL (Fin a) (Af E) ⧸ U)) (sand g (hOne E a)) (sand g v) = sand g (P y + Z) :=
    (hWd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by rw [h0, map_one]; rfl)).unique h2
  refine ⟨v + t • (P y + Z), ?_, ?_⟩
  · have h4 : ‖P y‖ ≤ K * ‖v‖ * B :=
      (P.le_opNorm y).trans (mul_le_mul hPn hb (norm_nonneg _) (by positivity))
    have h5 : ‖Z‖ ≤ B * ‖v‖ := hZ.trans (mul_le_mul_of_nonneg_left hn hB)
    have h6 : ‖t • (P y + Z)‖ ≤ ‖P y‖ + ‖Z‖ := by
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (norm_add_le _ _)
    have h7 := norm_add_le v (t • (P y + Z))
    nlinarith
  · rw [flow_der hWd, h3, map_add (sand g) v, map_smul]

end UpperTheory.V.Lit.Geo
