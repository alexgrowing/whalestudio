import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.HasStrictFDerivAtOneProd

noncomputable section

open Matrix Filter Topology
open scoped NNReal

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem norm_le_sum (X : Matrix (Fin n) (Fin n) ℂ) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : ((Finset.univ).sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)
  calc _ ≤ ((∑ i, ∑ j, ‖X i j‖₊ : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 this
    _ = _ := by push_cast; rfl

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := lieG G
  add_mem' := by
    intro X Y hX hY
    have hX' : Xᴴ * G + G * X = 0 := hX
    have hY' : Yᴴ * G + G * Y = 0 := hY
    show (X + Y)ᴴ * G + G * (X + Y) = 0
    rw [conjTranspose_add, add_mul, mul_add]
    calc _ = (Xᴴ * G + G * X) + (Yᴴ * G + G * Y) := by abel
      _ = 0 := by rw [hX', hY', add_zero]
  zero_mem' := zero_mem_lieG G
  smul_mem' := by
    intro c X hX
    have h := CCRuleCW.lie_smul G X hX c
    rw [Complex.coe_smul] at h
    exact h

theorem sobChart_holds : SobChart := by
  intro n G s _
  classical
  let L := lieSub G
  let d := Module.finrank ℝ L
  let b := Module.finBasis ℝ L
  let Y : Fin d → Matrix (Fin n) (Fin n) ℂ := fun i => (b i : Matrix (Fin n) (Fin n) ℂ)
  have hY : ∀ i, Y i ∈ lieG G := fun i => (b i).2
  refine ⟨d, Y, hY, ?_⟩
  let ψ : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := L.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : ∀ t, ψ t = lin Y t := by
    intro t
    simp [ψ, lin_apply, Y, Module.Basis.equivFun_symm_apply]
    try rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp b.equivFun.symm.injective
  obtain ⟨Q0, hQ0⟩ := ψ.exists_leftInverse_of_injective hinj
  let Q : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap Q0
  have hQψ : ∀ t, Q (ψ t) = t := fun t => LinearMap.congr_fun hQ0 t
  have hback : ∀ X ∈ lieG G, ψ (Q X) = X := by
    intro X hX
    have e : X = ψ (b.equivFun ⟨X, hX⟩) := by simp [ψ]
    rw [e, hQψ]
  let f : (Fin d → ℝ) → (Fin d → ℝ) := fun t => Q (cay (oneProd Y t))
  have hcay : HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (oneProd Y 0) := by
    rw [oneProd_zero]; exact hasStrictFDerivAt_cay
  have hΦ := hcay.comp (0 : Fin d → ℝ) (hasStrictFDerivAt_oneProd Y)
  have hf := Q.hasStrictFDerivAt.comp (0 : Fin d → ℝ) hΦ
  have hf' : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) 0 := by
    refine hf.congr_fderiv ?_
    ext1 t
    change Q (lin Y t) = t
    rw [← hψ]
    exact hQψ t
  have hmap := hf'.map_nhds_eq_of_equiv
  have hcay1 : cay (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [cay]
  have hf0 : f 0 = 0 := by
    show Q (cay (oneProd Y 0)) = 0
    rw [oneProd_zero, hcay1, map_zero]
  rw [hf0] at hmap
  intro ε hε
  have hcont : ContinuousAt (oneProd Y) 0 := (hasStrictFDerivAt_oneProd Y).continuousAt
  have hUnit : {t : Fin d → ℝ | IsUnit (oneProd Y t + 1)} ∈ 𝓝 (0 : Fin d → ℝ) := by
    have hc : ContinuousAt (fun t => oneProd Y t + 1) 0 := hcont.add continuousAt_const
    have h2 : IsUnit (oneProd Y 0 + 1) := by rw [oneProd_zero]; exact isUnit_two
    exact hc.preimage_mem_nhds (Units.isOpen.mem_nhds h2)
  have hB : Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)} ∈ 𝓝 (0 : Fin d → ℝ) :=
    Filter.inter_mem (Metric.ball_mem_nhds 0 hε) hUnit
  have hfB : f '' (Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)}) ∈ 𝓝 (0 : Fin d → ℝ) := by
    rw [← hmap]; exact Filter.image_mem_map hB
  have hk : ContinuousAt (fun g => Q (cay g)) (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Q.continuous.continuousAt.comp hasStrictFDerivAt_cay.continuousAt
  have hN : {g : Matrix (Fin n) (Fin n) ℂ | Q (cay g) ∈
      f '' (Metric.ball (0 : Fin d → ℝ) ε ∩ {t | IsUnit (oneProd Y t + 1)})} ∩ {g | IsUnit (g + 1)} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) := by
    refine Filter.inter_mem ?_ ?_
    · refine hk.preimage_mem_nhds ?_
      show _ ∈ 𝓝 (Q (cay 1))
      rw [hcay1, map_zero]
      exact hfB
    · have hc : ContinuousAt (fun g : Matrix (Fin n) (Fin n) ℂ => g + 1) 1 :=
        continuousAt_id.add continuousAt_const
      exact hc.preimage_mem_nhds (Units.isOpen.mem_nhds isUnit_two)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hδ : 0 < r / ((n : ℝ) * n + 1) := by positivity
  refine ⟨r / ((n : ℝ) * n + 1), hδ, ?_⟩
  intro g hg hgd
  have hnorm : ‖g - 1‖ < r := by
    calc ‖g - 1‖ ≤ ∑ i, ∑ j, ‖(g - 1) i j‖ := norm_le_sum _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, r / ((n : ℝ) * n + 1) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [Matrix.sub_apply]; exact (hgd i j).le
      _ = (n : ℝ) * n * (r / ((n : ℝ) * n + 1)) := by simp [Finset.sum_const, mul_assoc]
      _ < r := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hgN := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hnorm)
  obtain ⟨⟨t, ⟨htB, htU⟩, hft⟩, hgU⟩ := hgN
  refine ⟨t, fun i => ?_, ?_⟩
  · have h1 := norm_le_pi_norm t i
    have h2 := mem_ball_zero_iff.1 htB
    rw [Real.norm_eq_abs] at h1
    linarith
  · have e1 : cay (oneProd Y t) = cay g := calc
      cay (oneProd Y t) = ψ (Q (cay (oneProd Y t))) :=
          (hback _ (cay_mem G _ (oneProd_mem G Y hY t) htU)).symm
      _ = ψ (Q (cay g)) := congrArg ψ hft
      _ = cay g := hback _ (cay_mem G g hg hgU)
    exact (cay_inj htU hgU e1).symm

end Chart

theorem sobChart_holds : SobChart := Chart.sobChart_holds

end Formalism.IndefR.Tow.SobPf

end
