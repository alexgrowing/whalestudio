import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cinf_sq {E : Type} [Field E] (y : (Cinf E)ˣ) : ∃ r : (Cinf E)ˣ, r ^ 2 = y := by
  have hy : ∀ w, y.val w ≠ 0 := fun w h => by
    have := congrFun y.mul_inv w
    simp [h] at this
  choose z hz using fun w => IsAlgClosed.exists_pow_nat_eq (y.val w) (n := 2) (by norm_num)
  have hz0 : ∀ w, z w ≠ 0 := fun w h => hy w (by rw [← hz w, h]; simp)
  refine ⟨⟨z, fun w => (z w)⁻¹, funext fun w => mul_inv_cancel₀ (hz0 w), funext fun w => inv_mul_cancel₀ (hz0 w)⟩, Units.ext (funext fun w => ?_)⟩
  exact hz w

private theorem pInf_infId {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (r : (Cinf E)ˣ) :
    Units.map (pInf E).toMonoidHom (infId E r) = r := by
  have h : ∀ x, pInf E (GlobalTheory.CuspRep.sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  refine Units.ext ?_
  change pInf E (1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E r.val) = r.val
  simp [h]

private theorem dM_fin {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (t : (A E)ˣ)
    (ht : pInf E (t : A E) = 1) : ∃ k, dM t = finGL E 2 k := by
  refine ⟨GeneralLinearGroup.map (pFin E) (dM t), ?_⟩
  have h : GeneralLinearGroup.map (pInf E) (dM t) = 1 := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht]
  conv_lhs => rw [← infGL_mul_finGL (dM t), h, map_one, one_mul]

theorem UpperTheory.cuspSubspace_translate_eq_smul_special_translate :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → ∀ f ∈ P.V, ∀ x : GL (Fin 2) (A E), ∃ (c : ℂ) (f' : Sm E 2) (h : G1 E), f' ∈ P.V ∧ ∀ g, f.1 (g * x) = c * f'.1 (g * gl h) := by
  intro E _ _ _ P ω hω f hf x
  obtain ⟨g0, hg0⟩ := exists_gl_mul_dM x
  obtain ⟨r, hr⟩ := cinf_sq (Units.map (pInf E).toMonoidHom (GeneralLinearGroup.det x))
  obtain ⟨s, hs⟩ : ∃ s : (A E)ˣ, Units.map (pInf E).toMonoidHom s = r := ⟨infId E r, pInf_infId r⟩
  obtain ⟨t, ht⟩ : ∃ t : (A E)ˣ, GeneralLinearGroup.det x = s ^ 2 * t := ⟨(s ^ 2)⁻¹ * GeneralLinearGroup.det x, by group⟩
  have ht1 : pInf E (t : A E) = 1 := by
    have h1 : Units.map (pInf E).toMonoidHom t = 1 := by
      have h2 := congrArg (Units.map (pInf E).toMonoidHom) ht
      rw [map_mul, map_pow, hs, hr] at h2
      exact (mul_eq_left.1 h2.symm)
    exact congrArg Units.val h1
  obtain ⟨k, hk⟩ := dM_fin t ht1
  refine ⟨((ω.1 (ideleNorm ℚ E s) : ℂˣ) : ℂ), act (.fin k) f, g0 * (mD s)⁻¹, P.stable (.fin k) f hf, fun g => ?_⟩
  have hx : x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (g0 * (mD s)⁻¹) * dM t) := by
    have e : dM (s ^ 2) = (gl (mD s))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      rw [← gl_mD_mul_dM_sq, inv_mul_cancel_left]
    rw [gl_mul, gl_inv]
    conv_lhs => rw [hg0, ht, dM_mul, e]
    rw [scalar_comm s (gl g0 * (gl (mD s))⁻¹ * dM t), mul_assoc (gl (mD s))⁻¹, scalar_comm s (dM t)]
    simp only [mul_assoc]
  have hg : g * x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * gl (g0 * (mD s)⁻¹) * finGL E 2 k) := by
    rw [hx, hk, ← mul_assoc g, ← scalar_comm s g, mul_assoc, mul_assoc]
  rw [hg, hω f hf]
  rfl
