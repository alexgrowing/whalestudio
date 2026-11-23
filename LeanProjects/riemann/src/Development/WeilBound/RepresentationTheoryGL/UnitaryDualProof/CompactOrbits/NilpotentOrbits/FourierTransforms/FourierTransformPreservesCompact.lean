import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CharacteristicFunctionIntegralApply

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_mem (x : Matrix (Fin n) (Fin n) k) : Pr Z x ∈ B0 Z := E_mem Z _

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem quadratic_form_vanishes_nilpotent {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) : qL Z w = 0 := LinearMap.mem_ker.1 hw.2

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

theorem fourier_transform_vanishes_on_fibre (f : Sp k n → ℂ) {y : Fin (Module.finrank k Z) → k} (hf0 : ∀ q ∈ Fib Z y, f q = 0) {p : Sp k n}
    (hp : p ∈ Fib Z y) : phi0 ψ ν hZ h f p = 0 := by
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := by
    intro u
    apply hf0
    obtain ⟨⟨hB, hq⟩, -⟩ := hp
    have hw : E Z u - Pr Z p.1 ∈ B0 Z := Submodule.sub_mem _ (E_mem Z u) (Pr_mem _)
    have hw1 : E Z u - Pr Z p.1 ∈ BzL Z := (Submodule.mem_inf.mp hw).1
    have hw2 : qL Z (E Z u - Pr Z p.1) = 0 := quadratic_form_vanishes_nilpotent hw
    have heq : p.1 - Pr Z p.1 + E Z u = p.1 + (E Z u - Pr Z p.1) := by abel
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · show p.1 - Pr Z p.1 + E Z u ∈ BzL Z
      rw [heq]
      exact (BzL Z).add_mem hB hw1
    · have hadd := (qL Z).map_add p.1 (E Z u - Pr Z p.1)
      rw [hw2, add_zero] at hadd
      show qZ Z (p.1 - Pr Z p.1 + E Z u) = y
      rw [heq]
      exact hadd.trans hq
  simp [hz]

theorem fourier_transform_equivariant {g : GL (Fin n) k} (hg : g ∈ Gz Z) (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν hZ h (fun q => f (act g q)) p = phi0 ψ ν hZ h f (act g p) := by
  have hdet : (adM hg).det ≠ 0 := by
    intro h0
    have := det_adM_sq hZ h hg
    rw [h0] at this
    simp at this
  have hU : IsUnit (adM hg).det := isUnit_iff_ne_zero.mpr hdet
  let e : (Fin (d Z) → k) ≃ᵐ (Fin (d Z) → k) :=
    { toFun := fun u => adM hg *ᵥ u
      invFun := fun u => (adM hg)⁻¹ *ᵥ u
      left_inv := fun u => by simp [mulVec_mulVec, nonsing_inv_mul _ hU]
      right_inv := fun u => by simp [mulVec_mulVec, mul_nonsing_inv _ hU]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = Measure.pi fun _ => ν := by
    have := GlobalTheory.WeilM.smul_map_mulVec_pi ν (adM hg) (GeneralLinearGroup.det (adU hZ h hg)) rfl
    rw [distribHaarChar_adU] at this
    show Measure.map (fun u => adM hg *ᵥ u) _ = _
    simpa using this
  rw [characteristic_function_integral_apply, characteristic_function_integral_apply]
  conv_rhs => rw [← hmap, e.measurableEmbedding.integral_map]
  congr 1
  funext u
  have he : e u = adL hg u := adM_mulVec hg u
  simp only [act]
  rw [he, E_adL, Pr_conj hZ h hg, dot_conj]
  congr 3
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

theorem fourier_transform_preserves_compact {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    phi0 ψ ν hZ h f ∈ supportedIn (UU : Set (Sp k n)) := by
  have hm := test_vector_mem_schwartz_bruhat ψ ν hZ h hc (f := f) ⟨hf.1, Set.subset_univ _⟩
  refine ⟨hm.1, ?_⟩
  intro p hp
  by_contra hp2
  apply hp
  have h0 : p.2 = 0 := by
    by_contra hne
    exact hp2 hne
  rw [characteristic_function_integral_apply]
  have hz : ∀ u, f (p.1 - Pr Z p.1 + E Z u, p.2) = 0 := by
    intro u
    by_contra hne
    exact hf.2 hne h0
  simp [hz]

def Refl (p : Sp k n) : Sp k n := (p.1 - (2 : k) • Pr Z p.1, p.2)

omit [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Refl_Refl (p : Sp k n) : Refl (Z := Z) (Refl (Z := Z) p) = p := by
  have hPP : Pr Z (Pr Z p.1) = Pr Z p.1 := Pr_E hZ h _
  have hP : Pr Z (p.1 - (2 : k) • Pr Z p.1) = - Pr Z p.1 := by
    rw [sub_eq_add_neg, Pr_add, ← neg_smul, Pr_smul, hPP]
    module
  obtain ⟨x, v⟩ := p
  simp only [Refl] at hP ⊢
  rw [hP]
  ext <;> simp

theorem partial_fourier_first_coordinates (q : TT Z × (Fin (d Z) → k)) : Hb hZ h (F1 hZ h q) = (q.1, G Z *ᵥ q.2) := by
  simp only [F1, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  rfl

def Gu : GL (Fin (d Z)) k := Matrix.nonsingInvUnit (G Z) (Ne.isUnit (G_det hZ h))

theorem pf_G (F : TT Z × (Fin (d Z) → k) → ℂ) (z : TT Z × (Fin (d Z) → k)) :
    ∫ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) ∂(Measure.pi fun _ => ν) =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) F (z.1, (G Z)⁻¹ *ᵥ z.2) := by
  have hU : IsUnit (G Z).det := isUnit_iff_ne_zero.mpr (G_det hZ h)
  set c := distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) with hcdef
  have hc : c ≠ 0 := by
    intro h0
    have := map_mul (distribHaarChar k) (Matrix.GeneralLinearGroup.det (Gu hZ h))
      (Matrix.GeneralLinearGroup.det (Gu hZ h))⁻¹
    rw [mul_inv_cancel, map_one, ← hcdef, h0, zero_mul] at this
    exact zero_ne_one this.symm
  let e : (Fin (d Z) → k) ≃ᵐ (Fin (d Z) → k) :=
    { toFun := fun u => G Z *ᵥ u
      invFun := fun u => (G Z)⁻¹ *ᵥ u
      left_inv := fun u => by simp [mulVec_mulVec, nonsing_inv_mul _ hU]
      right_inv := fun u => by simp [mulVec_mulVec, mul_nonsing_inv _ hU]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have hsm := GlobalTheory.WeilM.smul_map_mulVec_pi ν (G Z) (Matrix.GeneralLinearGroup.det (Gu hZ h)) rfl
  rw [← hcdef] at hsm
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hmap : Measure.map e (Measure.pi fun _ : Fin (d Z) => ν) = (c : ENNReal)⁻¹ • Measure.pi fun _ => ν := by
    show Measure.map (G Z).mulVec _ = _
    conv_rhs => rw [← hsm]
    rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  let H : (Fin (d Z) → k) → ℂ := fun x => F (z.1, x) * (ψ (x ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
  have hH : ∀ u, F (z.1, G Z *ᵥ u) * (ψ (u ⬝ᵥ z.2) : ℂ) = H (e u) := by
    intro u
    show _ = F (z.1, G Z *ᵥ u) * (ψ ((G Z *ᵥ u) ⬝ᵥ (G Z)⁻¹ *ᵥ z.2) : ℂ)
    rw [dotProduct_mulVec, vecMul_mulVec, ← Matrix.mulVec_transpose, G_symm, mul_nonsing_inv _ hU,
      transpose_one, one_mulVec]
  rw [integral_congr_ae (ae_of_all _ hH), ← e.measurableEmbedding.integral_map, hmap, integral_smul_measure]
  simp [GlobalTheory.SplitDict.pf, H]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
