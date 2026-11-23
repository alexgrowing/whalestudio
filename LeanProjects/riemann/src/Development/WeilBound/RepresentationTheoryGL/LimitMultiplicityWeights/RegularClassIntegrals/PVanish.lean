import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PVanish

def mul3 {n : ℕ} (A B C : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n := fun a b => (of A * of B * of C) a b

theorem contDiff_triple_matrix_product {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → MainStatements.WeightKernel.Mx n}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun x => mul3 (f x) (g x) (h x) := by
  have e : ∀ (u : E → Mx n), ContDiff ℝ ∞ u → ∀ a b : Fin n, ContDiff ℝ ∞ fun x => u x a b :=
    fun u hu a b => contDiff_pi.1 (contDiff_pi.1 hu a) b
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [mul3, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun j _ =>
    (ContDiff.sum fun k _ => (e f hf a k).mul (e g hg k j)).mul (e h hh j b)

theorem triple_product_matrix_coordinates {H : Type} [Group H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (g h l : H) :
    mul3 (matCoord ι g) (matCoord ι h) (matCoord ι l) = matCoord ι (g * h * l) := by
  funext a b
  show (ι g * ι h * ι l) a b = ι (g * h * l) a b
  rw [map_mul, map_mul]

end MainStatements.WeightKernel.PVanish

open MainStatements.WeightKernel.PVanish in
theorem MainStatements.WeightKernel.vanish : KerSwap → IdentOne → IdentTwo → Vanish := by
  intro hSwap hOne hTwo H _ _ _ _ _ _ _ _ n ι hemb s B hB μ _ _ dt _ _ Ω I _ _ m _ c q hK hq hInv φ hφ hOrb
  obtain ⟨hφc, Φφ, hΦφ, hφeq⟩ := hφ
  have hmc : Continuous (matCoord ι) := hemb.continuous
  have hφcont : Continuous φ := by
    rw [show φ = fun g => Φφ (matCoord ι g) from funext hφeq]
    exact hΦφ.continuous.comp hmc
  let bp : ContDiffBump (matCoord ι s) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : H → ℝ := fun y => bp (matCoord ι y)
  have hψc : Continuous ψ := bp.continuous.comp hmc
  have hψcs : HasCompactSupport ψ := bp.hasCompactSupport.comp_isClosedEmbedding hemb
  have hψs : 0 < ψ s := by
    have : ψ s = 1 := bp.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
    rw [this]
    exact one_pos
  obtain ⟨a, ha0, ha⟩ := hOne H n ι hmc s B hB μ dt ψ hψc hψcs (fun y => bp.nonneg) hψs
  obtain ⟨Kset, hKc, hKprop⟩ := hB.proper (tsupport φ) (tsupport ψ) hφc.isCompact hψcs.isCompact
  let p : H → Mx n × Mx n := fun k => (matCoord ι k, matCoord ι k⁻¹)
  have hp : Continuous p := hmc.prodMk (hmc.comp continuous_inv)
  let W₁ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ z.1 * ((B (z.1, z.2.1) : ℝ) : ℂ) * ((bp (mul3 z.2.2 z.1 z.2.1) : ℝ) : ℂ)
  let W₂ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ (mul3 z.2.1 z.1 z.2.2) * ((B (mul3 z.2.1 z.1 z.2.2, z.2.1) : ℝ) : ℂ) * ((bp z.1 : ℝ) : ℂ)
  have hfst : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.1 := contDiff_fst
  have hA : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hC : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.2 := contDiff_snd.comp contDiff_snd
  have hM1 := contDiff_triple_matrix_product hC hfst hA
  have hM2 := contDiff_triple_matrix_product hA hfst hC
  have hW₁ : ContDiff ℝ ∞ W₁ :=
    ((hΦφ.comp hfst).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hfst.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hM1))
  have hW₂ : ContDiff ℝ ∞ W₂ :=
    ((hΦφ.comp hM2).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hM2.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hfst))
  have hW₁pt : ∀ y k : H, W₁ (matCoord ι y, p k) =
      φ y * ((B (matCoord ι y, matCoord ι k) : ℂ) * (ψ (k⁻¹ * y * k) : ℂ)) := by
    intro y k
    simp only [W₁, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq, mul_assoc]
  have hW₂pt : ∀ y k : H, W₂ (matCoord ι y, p k) =
      φ (k * y * k⁻¹) * (B (matCoord ι (k * y * k⁻¹), matCoord ι k) : ℂ) * (ψ y : ℂ) := by
    intro y k
    simp only [W₂, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq]
  have hvan1 : ∀ z k : H, k ∉ Kset → W₁ (matCoord ι (z⁻¹ * s * z), p k) = 0 := by
    intro z k hk
    rw [hW₁pt]
    by_contra hne
    apply hk
    have h1 : φ (z⁻¹ * s * z) ≠ 0 := left_ne_zero_of_mul hne
    have h23 := right_ne_zero_of_mul hne
    have h2 : (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) ≠ 0 := left_ne_zero_of_mul h23
    have h3 : (ψ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ≠ 0 := right_ne_zero_of_mul h23
    have e : (z * k)⁻¹ * s * (z * k) = k⁻¹ * (z⁻¹ * s * z) * k := by group
    refine hKprop z k (subset_tsupport _ h1) ?_ (fun h0 => h2 (by simp [h0]))
    rw [e]
    exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
  have hvan2 : ∀ w k : H, k ∉ Kset → W₂ (matCoord ι (w⁻¹ * s * w), p k) = 0 := by
    intro w k hk
    rw [hW₂pt]
    by_contra hne
    apply hk
    have h12 := left_ne_zero_of_mul hne
    have h3 : (ψ (w⁻¹ * s * w) : ℂ) ≠ 0 := right_ne_zero_of_mul hne
    have h1 : φ (k * (w⁻¹ * s * w) * k⁻¹) ≠ 0 := left_ne_zero_of_mul h12
    have h2 : (B (matCoord ι (k * (w⁻¹ * s * w) * k⁻¹), matCoord ι k) : ℂ) ≠ 0 :=
      right_ne_zero_of_mul h12
    have e1 : (w * k⁻¹)⁻¹ * s * (w * k⁻¹) = k * (w⁻¹ * s * w) * k⁻¹ := by group
    have e2 : (w * k⁻¹ * k)⁻¹ * s * (w * k⁻¹ * k) = w⁻¹ * s * w := by group
    refine hKprop (w * k⁻¹) k ?_ ?_ ?_
    · rw [e1]
      exact subset_tsupport _ h1
    · rw [e2]
      exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
    · rw [e1]
      exact fun h0 => h2 (by simp [h0])
  have h1 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₁ p Kset (tsupport φ) hW₁ hp hKc
    hφc.isCompact (by
      intro k _ y hy
      have : φ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₁pt, this, zero_mul])
  have h2 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₂ p Kset (tsupport ψ) hW₂ hp hKc
    hψcs.isCompact (by
      intro k _ y hy
      have : ψ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₂pt, this]
      simp)
  have hR1 : ∫ x, ker c q (fun y => ∫ k in Kset, W₁ (matCoord ι y, p k) ∂μ) x ∂m =
      a * ∫ x, ker c q φ x ∂m := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [MainStatements.WeightKernel.ker]
    rw [← tsum_mul_left]
    congr 1
    funext i
    obtain ⟨z, hz⟩ := hq i x
    rw [hz, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan1 z)]
    simp only [hW₁pt]
    rw [integral_const_mul, ha z]
    ring
  have hstep : ∀ k : H, ∫ x, ker c q (fun y => W₁ (matCoord ι y, p k)) x ∂m =
      ∫ x, ker c q (fun y => W₂ (matCoord ι y, p k)) x ∂m := by
    intro k
    have hmem : (fun y => W₂ (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨?_, fun Y => W₂ (Y, p k), hW₂.comp (contDiff_id.prodMk contDiff_const), fun g => rfl⟩
      refine hψcs.mono ?_
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      apply hy
      rw [hW₂pt, h0]
      simp
    have hfun : (fun y => W₁ (matCoord ι y, p k)) =
        fun y => W₂ (matCoord ι (k⁻¹ * y * k⁻¹⁻¹), p k) := by
      funext y
      rw [hW₂pt, hW₁pt]
      have e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
      rw [e, inv_inv]
      ring
    rw [hfun]
    exact hInv _ hmem k⁻¹
  have hR2 : ∫ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x ∂m = 0 := by
    have hz : ∀ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x = 0 := by
      intro x
      simp only [MainStatements.WeightKernel.ker]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      obtain ⟨w, hw⟩ := hq i x
      rw [hw, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan2 w)]
      simp only [hW₂pt]
      rw [integral_mul_const, hTwo H n ι hmc s B hB μ dt φ hφcont hφc hOrb w]
      simp
    simp [hz]
  have key : a * ∫ x, ker c q φ x ∂m = 0 := by
    rw [← hR1, ← h1]
    simp only [hstep]
    rw [h2]
    exact hR2
  exact (mul_eq_zero.1 key).resolve_left ha0

end
