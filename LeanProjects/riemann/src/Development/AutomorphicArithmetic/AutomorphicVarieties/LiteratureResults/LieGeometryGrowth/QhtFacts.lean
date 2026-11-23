import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormVecMulGeOfHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem qht_le (g : GA E a) (γ : GL (Fin a) E) :
    qht g ≤ height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) :=
  ciInf_le ⟨1, by rintro _ ⟨δ, rfl⟩; exact one_le_height _⟩ γ

private theorem one_le_qht (g : GA E a) : 1 ≤ qht g := le_ciInf fun _ => one_le_height _

private theorem retract_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem qht_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    qht (ratGL E a γ * splitCentre E a t * g) = qht g := by
  unfold qht
  rw [retract_left]
  refine Eq.trans ?_ ((Equiv.mulRight γ).iInf_comp
    (g := fun δ : GL (Fin a) E => height (K := E) (ratGL E a δ * (retractOne g : KernelIndexFullLattice.G1 E a).1)))
  refine congrArg _ (funext fun δ => ?_)
  rw [Equiv.coe_mulRight, map_mul, mul_assoc]

private theorem exists_split (g : GA E a) : ∃ t : ℝ, splitCentre E a t * g = (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

private theorem qht_mul {C : Set (GA E a)} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ g : GA E a, ∀ h ∈ C, qht (g * h) ≤ B * qht g := by
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (K := E) (n := a)
    (hC.image (continuous_subtype_val.comp (continuous_retractOne (K := E) (n := a))))
  have hc : 0 < heightConst E a := one_pos.trans_le one_le_heightConst
  refine ⟨heightConst E a * M, fun g h hh => ?_⟩
  have hm := hM _ ⟨h, hh, rfl⟩
  have hM0 : 0 < M := (height_pos _).trans_le hm
  rw [← div_le_iff₀' (mul_pos hc hM0)]
  refine le_ciInf fun γ => ?_
  rw [div_le_iff₀' (mul_pos hc hM0)]
  refine (qht_le _ γ).trans ?_
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, mul_right_comm]
  exact (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left hm (mul_pos hc (height_pos _)).le)

private theorem qht_proper (R : ℝ) : ∃ C : Set (GA E a), IsCompact C ∧
    ∀ g : GA E a, qht g ≤ R → ∃ γ t, ratGL E a γ * splitCentre E a t * g ∈ C := by
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height E a
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := E) (n := a)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hg.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨t, ht⟩ := exists_split g
  obtain ⟨_, ⟨δ, rfl⟩, x, hx, e⟩ := hC' (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
    (mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) (retractOne g).2) fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v hv
      have hp : 0 ≤ Reduction.height (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) v := by
        by_contra hn
        have : 0 ≤ c * height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1) ^ N := by
          have := height_pos (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_pos _).le hγ.le N) hc.le) hp)
  refine ⟨δ⁻¹ * γ, t, ?_⟩
  have e' : ratGL E a δ * x = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := e
  rw [mul_assoc, ht, map_mul, mul_assoc, ← e', map_inv, inv_mul_cancel_left]
  exact hx

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.qhtFacts :
    QhtFacts := by
  intro E _ _ _ a
  exact ⟨one_le_qht, qht_left, fun _ hC => qht_mul hC, qht_proper⟩
