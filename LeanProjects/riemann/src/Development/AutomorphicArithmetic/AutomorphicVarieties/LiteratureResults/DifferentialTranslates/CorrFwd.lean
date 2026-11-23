import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvK

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem cont_multi {V F ι : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : MultilinearMap ℝ (fun _ : ι => V) F) : Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : (f : (ι → V) → F) = fun v => ∑ r : ι → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (v i)) • f fun i => b (r i) := by
    funext v
    have e : v = fun i => ∑ j, b.coord j (v i) • b j := funext fun i => (b.sum_repr (v i)).symm
    conv_lhs => rw [e]
    rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  exact continuous_finset_sum _ fun r _ => (continuous_finset_prod _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)).smul continuous_const

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def back (g : GL (Fin a) (Cinf E)) : HV E a →ₗ[ℝ] Herm E a :=
  (hv.symm : HV E a ≃ₗ[ℝ] Herm E a).toLinearMap ∘ₗ ((2⁻¹ : ℝ) • (sand g⁻¹).toLinearMap)

private theorem back_apply (g : GL (Fin a) (Cinf E)) (v : HV E a) :
    back g v = hv.symm ((2⁻¹ : ℝ) • sand g⁻¹ v) := rfl

private theorem sand_sand (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem back_sand (g : GL (Fin a) (Cinf E)) (X : Herm E a) : back g ((2 : ℝ) • sand g (hv X)) = X := by
  rw [back_apply, map_smul (sand g⁻¹), smul_smul, sand_sand, inv_mul_cancel, map_one, inv_mul_cancel₀ two_ne_zero, one_smul]
  exact hv.symm_apply_apply X

private theorem adHerm_back (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (v : HV E a) :
    adHerm k (back (g * Unitary.toUnits k) v) = back g v := by
  have h : ∀ y : HV E a, adHerm k (hv.symm y) = hv.symm (sand (Unitary.toUnits k) y) := fun _ => rfl
  rw [back_apply, back_apply, h, map_smul, sand_sand, _root_.mul_inv_rev, mul_inv_cancel_left]

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_sand, ← e, sand_sand, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

variable [IsTotallyComplex E] (Ξ : AlgRep E a) {q : ℕ}
  (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)))

private def alt (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→ₗ[ℝ] (Fin Ξ.d → ℂ) :=
  ((Matrix.toLin' (Ξ.mat g) ∘ₗ (LinearMap.proj (infGL E a g * finGL E a x) : (GA E a → Fin Ξ.d → ℂ) →ₗ[ℂ] (Fin Ξ.d → ℂ)) ∘ₗ
    ev).restrictScalars ℝ).compAlternatingMap (α.compLinearMap (back g))

private theorem alt_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    alt Ξ α g x v = Ξ.mat g *ᵥ ev (α fun i => back g (v i)) (infGL E a g * finGL E a x) := rfl

private def altL (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) : HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ) :=
  { alt Ξ α g x with cont := cont_multi (alt Ξ α g x).toMultilinearMap }

private theorem altL_apply (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (v : Fin q → HV E a) :
    altL Ξ α g x v = alt Ξ α g x v := rfl

private theorem alt_cpt (hα : IsCochain (smK Ξ) α) (g : GL (Fin a) (Cinf E)) (k : Kinf E a) (x : GL (Fin a) (Af E))
    (v : Fin q → HV E a) : alt Ξ α (g * Unitary.toUnits k) x v = alt Ξ α g x v := by
  have h := hα k fun i => back (g * Unitary.toUnits k) (v i)
  simp only [adHerm_back] at h
  rw [alt_apply, alt_apply, h, evK, Matrix.mulVec_mulVec, ← map_mul Ξ.mat, map_mul (infGL E a), mul_assoc, mul_assoc,
    infGL_comm]

private theorem alt_fin {U : Subgroup (GL (Fin a) (Af E))} (hU : ∀ X, RightInv U (α X)) (g : GL (Fin a) (Cinf E))
    (x : GL (Fin a) (Af E)) {u : GL (Fin a) (Af E)} (hu : u ∈ U) (v : Fin q → HV E a) :
    alt Ξ α g (x * u) v = alt Ξ α g x v := by
  rw [alt_apply, alt_apply, map_mul (finGL E a), ← mul_assoc, hU _ u hu]

end UpperTheory.V.Lit.Dr

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.corrFwd :
    CorrFwd := by
  classical
  intro E _ _ _ a U Ξ q α hα hU
  refine ⟨fun s p => if h : p ∈ cone E a then altL Ξ α h.choose s.out else 0, fun g x X => ?_,
    fun s p hp => dif_neg hp⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dif_pos hp, altL_apply, hk, hu, alt_cpt Ξ α hα, alt_fin Ξ α hU _ _ u.2, alt_apply]
  simp only [back_sand]
