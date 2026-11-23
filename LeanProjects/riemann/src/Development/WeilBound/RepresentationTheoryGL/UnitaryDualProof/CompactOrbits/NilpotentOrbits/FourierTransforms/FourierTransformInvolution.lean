import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourierTransformPreservesCompact

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (hZ : CR Z) (h : Hyp Z)

include hZ h

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (p : Sp k n) :
    phi0 ψ ν hZ h (phi0 ψ ν hZ h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu hZ h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (d Z) : ℝ)) : ℂ) * f (Refl (Z := Z) p) := by
  have h1 : (fun q => f (F1 hZ h q)) ∈ SB (TT Z × (Fin (d Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 hZ h)).1 hf.1
  have e : ∀ q, phi0 ψ ν hZ h f (F1 hZ h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) (q.1, G Z *ᵥ q.2) := by
    intro q
    show GlobalTheory.SplitDict.pf _ _ _ (Hb hZ h (F1 hZ h q)) = _
    rw [partial_fourier_first_coordinates]
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν hZ h f (F1 hZ h q)) (Hb hZ h p) = _
  simp only [e]
  show ∫ u, GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ => ν) (fun q => f (F1 hZ h q)) ((Hb hZ h p).1, G Z *ᵥ u) *
      (ψ (u ⬝ᵥ (Hb hZ h p).2) : ℂ) ∂(Measure.pi fun _ => ν) = _
  rw [pf_G ψ ν hZ h, GlobalTheory.SplitDict.pf_pf ν hc h1]
  simp only [real_test_function_apply, Fintype.card_fin]
  have e2 : ((Hb hZ h p).1.1 : Matrix (Fin n) (Fin n) k) + E Z (-((G Z)⁻¹ *ᵥ (Hb hZ h p).2)) =
      p.1 - (2 : k) • Pr Z p.1 := by
    rw [E_neg]
    show p.1 - Pr Z p.1 + -(E Z ((G Z)⁻¹ *ᵥ D Z p.1)) = _
    rw [← Pr, two_smul]
    abel
  have e3 : (Hb hZ h p).1.2 = p.2 := rfl
  rw [e2, e3]
  simp only [Refl]
  ring

def Tu (t : kˣ) : GL (Fin (d Z)) k := Units.map (Matrix.scalar (Fin (d Z)) : k →+* Matrix (Fin (d Z)) (Fin (d Z)) k) t

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_mulVec (t : kˣ) (u : Fin (d Z) → k) : (Tu (Z := Z) t).val *ᵥ u = (t : k) • u := by
  funext i
  simp [Tu, Matrix.scalar_apply, mulVec_diagonal]

omit hZ h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Tu_det (t : kˣ) : Matrix.GeneralLinearGroup.det (Tu (Z := Z) t) = t ^ d Z := by
  ext
  simp [Tu, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

theorem fourier_transform_scaling (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p ∈ Bz Z ×ˢ Set.univ) :
    phi0 ψ ν hZ h f (sig Z t p) =
      ((((nabs k t)⁻¹ ^ d Z : ℝ)) : ℂ) * phi0 ψ ν hZ h (fun q => f (sig Z t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp.1
  have hDy : D Z (x - Pr Z x) = 0 := D_sub_Pr hZ h x
  have hPy : Pr Z (x - Pr Z x) = 0 := Pr_of_D hZ h hDy
  have hpi : piZ Z x = x - Pr Z x := piZ_eq_sub hZ h hx
  have hsig : (sig Z t (x, v)) = (x - Pr Z x + (t : k) • Pr Z x, v) := by
    simp only [sig, hpi, sub_sub_cancel]
  rw [hsig, characteristic_function_integral_apply, characteristic_function_integral_apply]
  have hP : Pr Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • Pr Z x := by
    rw [Pr_add, hPy, Pr_smul, show Pr Z (Pr Z x) = Pr Z x from Pr_E hZ h _, zero_add]
  have hD : D Z (x - Pr Z x + (t : k) • Pr Z x) = (t : k) • D Z x := by
    rw [D_add, hDy, D_smul, D_Pr hZ h, zero_add]
  simp only [hP, hD, add_sub_cancel_right]
  have hyB : ∀ u, x - Pr Z x + E Z u ∈ Bz Z := fun u =>
    (BzL Z).add_mem ((BzL Z).sub_mem hx (Pr_mem x).1) (E_mem Z u).1
  have hpi2 : ∀ u, piZ Z (x - Pr Z x + E Z u) = x - Pr Z x := fun u => by
    rw [piZ_eq_sub hZ h (hyB u), Pr_add, hPy, Pr_E hZ h, zero_add, add_sub_cancel_right]
  have hs : ∀ u, sig Z t⁻¹ (x - Pr Z x + E Z u, v) = (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) := fun u => by
    simp only [sig, hpi2, add_sub_cancel_left, E_smul, Units.val_inv_eq_inv_val]
  simp only [hs]
  have key := GlobalTheory.WeilM.integral_comp_mulVec ν (Tu (Z := Z) t)
    (fun u => f (x - Pr Z x + E Z ((t⁻¹ : k) • u), v) * (ψ (u ⬝ᵥ D Z x) : ℂ))
  have ht : (t : k) ≠ 0 := t.ne_zero
  simp only [Tu_mulVec, Tu_det, map_pow, smul_smul, inv_mul_cancel₀ ht, one_smul, smul_dotProduct,
    ← dotProduct_smul] at key
  rw [← key]
  have hn : (nabs k t : ℝ) = ((distribHaarChar k t : NNReal) : ℝ) := rfl
  have hpos : (nabs k t : ℝ) ≠ 0 := by rw [hn]; exact_mod_cast (distribHaarChar_pos).ne'
  rw [NNReal.coe_pow, ← hn]
  push_cast
  have hposC : ((nabs k t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hposC, one_pow, one_mul]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
