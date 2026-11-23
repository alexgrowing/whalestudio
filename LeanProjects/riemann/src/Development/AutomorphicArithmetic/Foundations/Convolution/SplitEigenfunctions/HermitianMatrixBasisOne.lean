import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ActRat

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

section
variable {E : Type} [Field E] [NumberField E]

private noncomputable def mm (D : Dat ℚ E) (u t : ℚ) : E := algebraMap ℚ E u + algebraMap ℚ E t * D.θ

private noncomputable def hm (D : Dat ℚ E) (ξ : Fin 4 → ℚ) : Matrix (Fin 2) (Fin 2) E :=
  !![mm D (ξ 1) 0, mm D (ξ 2) (ξ 3); mm D (ξ 2) (-ξ 3), mm D (ξ 0) 0]

private theorem mm_base (D : Dat ℚ E) (u : ℚ) : mm D u 0 = algebraMap ℚ E u := by simp [mm]

private theorem σ_alg (D : Dat ℚ E) (u : ℚ) : D.σ (algebraMap ℚ E u) = algebraMap ℚ E u := D.σ.commutes u

private theorem σ_mm (D : Dat ℚ E) (u t : ℚ) : D.σ (mm D u t) = mm D u (-t) := by
  simp only [mm, map_add, map_mul, σ_alg, D.conj, map_neg]; ring

private theorem mm_mul (D : Dat ℚ E) (u t : ℚ) :
    mm D u t * mm D u (-t) = algebraMap ℚ E (u ^ 2 - D.δ * t ^ 2) := by
  have h := D.sq
  simp only [mm, map_sub, map_mul, map_pow, map_neg, ← h]; ring

private theorem herm_rp (D : Dat ℚ E) (ξ : Fin 4 → ℚ) :
    D.herm (rp ξ) = (hm D ξ).map (algebraMap E (A E)) := by
  have h0 : (0 : A ℚ) = rt (0 : ℚ) := (map_zero _).symm
  have hn : -(rt (ξ 3) : A ℚ) = rt (-ξ 3) := (map_neg _ _).symm
  ext i j
  fin_cases i <;> fin_cases j
  · change D.mkE (rt (ξ 1)) 0 = rt (mm D (ξ 1) 0)
    rw [h0, D.mkE_rt]; rfl
  · exact D.mkE_rt _ _
  · change D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (mm D (ξ 2) (-ξ 3))
    rw [hn, D.mkE_rt]; rfl
  · change D.mkE (rt (ξ 0)) 0 = rt (mm D (ξ 0) 0)
    rw [h0, D.mkE_rt]; rfl

private theorem act_iff (D : Dat ℚ E) (γ : SpecialLinearGroup (Fin 2) E) (ξ η : Fin 4 → ℚ) :
    D.act (gl (ratS E γ)) (rp ξ) = rp η ↔ γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ = hm D η := by
  haveI := AdeleBaseChange.nontrivial_adeleRing E
  have inj : Function.Injective fun X : Matrix (Fin 2) (Fin 2) E => X.map (algebraMap E (A E)) :=
    Matrix.map_injective (algebraMap E (A E)).injective
  have hγ : ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) = γ.1.map (algebraMap E (A E)) := by
    ext i j; exact ratS_apply γ i j
  have hs : D.star2 ((gl (ratS E γ)) : Matrix (Fin 2) (Fin 2) (A E)) =
      ((γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    ext i j
    rw [D.conjTransposeGal_apply, hγ]
    exact D.bar_rt _
  have hact : D.herm (D.act (gl (ratS E γ)) (rp ξ)) =
      (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    rw [D.herm_act, hs, herm_rp, hγ, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    apply inj
    change (γ.1 * hm D ξ * (γ.1.map D.σ)ᵀ).map (algebraMap E (A E)) = (hm D η).map (algebraMap E (A E))
    rw [← hact, h, herm_rp]
  · intro h
    apply D.herm_injective
    rw [hact, h, herm_rp]

private theorem hermitianMatrix_basisOne (D : Dat ℚ E) (r : ℚ) : hm D ![0, r, 0, 0] = !![algebraMap ℚ E r, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hm, mm]

private theorem prod_pow_unitVector_val (D : Dat ℚ E) (g : Matrix (Fin 2) (Fin 2) E) (R : E) :
    g * !![R, 0; 0, 0] * (g.map D.σ)ᵀ =
      !![g 0 0 * R * D.σ (g 0 0), g 0 0 * R * D.σ (g 1 0); g 1 0 * R * D.σ (g 0 0), g 1 0 * R * D.σ (g 1 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem prod_low (D : Dat ℚ E) (w R : E) :
    (!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E) * !![R, 0; 0, 0] * ((!![1, 0; w, 1] : Matrix (Fin 2) (Fin 2) E).map D.σ)ᵀ =
      !![R, R * D.σ w; w * R, w * R * D.σ w] := by
  rw [prod_pow_unitVector_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem δ_neg (D : Dat ℚ E) : D.δ < 0 := by
  have h := D.neg (algebraMap ℚ ℝ)
  simpa using h

private theorem rank_one (D : Dat ℚ E) (ξ : Fin 4 → ℚ) (h0 : ξ ≠ 0) (hq : qr D.δ ξ = 0) :
    ∃ (γ : SpecialLinearGroup (Fin 2) E) (r : ℚ), r ≠ 0 ∧ rp ξ = D.act (gl (ratS E γ)) (rp ![0, r, 0, 0]) := by
  have hq' : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 = ξ 1 * ξ 0 := by
    have : ξ 2 ^ 2 - D.δ * ξ 3 ^ 2 - ξ 1 * ξ 0 = 0 := hq
    linarith
  by_cases hx : ξ 1 = 0
  · have hδ := δ_neg D
    rw [hx, zero_mul] at hq'
    have h3 : ξ 3 = 0 := by
      by_contra h
      have : 0 < ξ 3 ^ 2 := by positivity
      nlinarith [sq_nonneg (ξ 2)]
    have h2 : ξ 2 = 0 := by
      rw [h3] at hq'
      simpa using hq'
    have hy : ξ 0 ≠ 0 := fun hy => h0 (by
      ext i; fin_cases i <;> simp [hy, hx, h2, h3])
    refine ⟨⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩, ξ 0, hy, ((act_iff D _ _ _).2 ?_).symm⟩
    rw [hermitianMatrix_basisOne, prod_pow_unitVector_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm, mm, hx, h2, h3]
  · have hx' : algebraMap ℚ E (ξ 1) ≠ 0 := by simpa using hx
    obtain ⟨w, hw, hσ⟩ : ∃ w : E, w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (-ξ 3) ∧
        D.σ w * algebraMap ℚ E (ξ 1) = mm D (ξ 2) (ξ 3) :=
      ⟨mm D (ξ 2) (-ξ 3) / algebraMap ℚ E (ξ 1), div_mul_cancel₀ _ hx', by
        rw [map_div₀, σ_mm, σ_alg, neg_neg, div_mul_cancel₀ _ hx']⟩
    refine ⟨⟨!![1, 0; w, 1], by simp [Matrix.det_fin_two]⟩, ξ 1, hx, ((act_iff D _ _ _).2 ?_).symm⟩
    have hmul := mm_mul D (ξ 2) (ξ 3)
    rw [hq', map_mul] at hmul
    change !![1, 0; w, 1] * _ * _ = _
    rw [hermitianMatrix_basisOne, prod_low, hm, mm_base, mm_base]
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change algebraMap ℚ E (ξ 1) * D.σ w = mm D (ξ 2) (ξ 3)
      rw [mul_comm]; exact hσ
    · exact hw
    · change w * algebraMap ℚ E (ξ 1) * D.σ w = algebraMap ℚ E (ξ 0)
      rw [hw]
      apply mul_left_cancel₀ hx'
      linear_combination mm D (ξ 2) (-ξ 3) * hσ + hmul
end

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orb1 :
    Orb1 := by
  intro E _ _ _ D
  refine ⟨fun γ => ?_, fun ξ h0 hq => rank_one D ξ h0 hq, fun γ r r' hr h => ?_, fun γ hγ => ?_, fun u r => ?_⟩
  · obtain ⟨N, -, hN⟩ := actRat ℚ E D (Matrix.SpecialLinearGroup.toGL γ)
    refine ⟨Matrix.toLin'OfInv (M := (N⁻¹ : GL (Fin 4) ℚ).val) (M' := N.val) (by simp) (by simp), fun ξ => ?_⟩
    rw [gl_ratS, hN]
    rfl
  · rw [act_iff, hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val] at h
    have h11 := congrFun (congrFun h 1) 1
    simpa [hr] using h11
  · set a := D.b.repr (γ.1 0 0) 0
    set t := D.b.repr (γ.1 0 0) 1
    have ha : γ.1 0 0 = mm D a t := by
      have h := D.b.sum_repr (γ.1 0 0)
      rw [Fin.sum_univ_two, D.b0, D.b1] at h
      rw [mm, ← h]
      simp [a, t, Algebra.smul_def]
    have hdet : γ.1 0 0 * γ.1 1 1 = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      have h10 : γ.1 1 0 = 0 := hγ
      simpa [h10] using h
    have hne : γ.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hnorm : γ.1 0 0 * D.σ (γ.1 0 0) = algebraMap ℚ E (a ^ 2 - D.δ * t ^ 2) := by
      rw [ha, σ_mm, mm_mul]
    refine ⟨a ^ 2 - D.δ * t ^ 2, fun hc => ?_, fun r => ?_⟩
    · rw [hc, map_zero] at hnorm
      exact (mul_ne_zero hne (by simpa using hne)) hnorm
    · refine (act_iff D _ _ _).2 ?_
      have h10 : γ.1 1 0 = 0 := hγ
      have h00 : γ.1 0 0 * algebraMap ℚ E r * D.σ (γ.1 0 0) = algebraMap ℚ E ((a ^ 2 - D.δ * t ^ 2) * r) := by
        rw [map_mul, ← hnorm]; ring
      rw [hermitianMatrix_basisOne, hermitianMatrix_basisOne, prod_pow_unitVector_val, h10, h00]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · obtain ⟨a, b, rfl⟩ := D.exists_mkE u
    rw [D.act_nU]
    ext i
    fin_cases i <;> simp [rp]
