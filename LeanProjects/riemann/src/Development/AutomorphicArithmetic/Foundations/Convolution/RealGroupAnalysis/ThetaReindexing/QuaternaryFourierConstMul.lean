import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.FtAct
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem diagonalConj_mul {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (g g' : G1 F) :
    cD t (g * g') = cD t g * cD t g' := by
  have ht : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv t
  apply Subtype.ext
  ext i j
  show (cD t (g * g')).1 i j = ((cD t g).1 * (cD t g').1) i j
  fin_cases i <;> fin_cases j
  · simp [cD, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(g.1 0 1 * g'.1 1 0)) * ht
  · simp [cD, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [cD, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [cD, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(g.1 1 0 * g'.1 0 1)) * ht

private theorem diagonalConj_one {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    cD t (1 : G1 F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem diagonalConj_unipotent {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (b : A F) :
    cD t (nU b) = nU (b * ((t⁻¹ : (A F)ˣ) : A F)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, nU]

private theorem diagonalConj_weyl {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    cD t (wW F) = mD t⁻¹ * wW F := by
  apply Subtype.ext
  ext i j
  show (cD t (wW F)).1 i j = ((mD t⁻¹).1 * (wW F).1) i j
  fin_cases i <;> fin_cases j <;> simp [cD, mD, wW, Matrix.mul_apply, Fin.sum_univ_two]

private theorem idelicNorm_inv {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : ab t⁻¹ = (ab t)⁻¹ := by
  simp [ab, map_inv]

private theorem idelicNorm_pos {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : 0 < ab t :=
  (IdeleGroup.ideleModule F t).2

private theorem similitude_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : GL (Fin 2) (A E)) : nu F h⁻¹ = (nu F h)⁻¹ := by
  simp [nu, map_inv]

private theorem quaternaryFourier_const_mul {F : Type} [Field F] [NumberField F] (δ : F) (c : ℂ) (f : V4 F → ℂ) (v : V4 F) :
    ft4 δ (fun y => c * f y) v = c * ft4 δ f v := by
  simp only [ft4, mul_assoc]
  exact integral_const_mul c _

theorem UpperTheory.ConvolutionTheory.R2.D.comm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)) (L : GL (Fin 2) (A E) →* Module.End ℂ (S4 F)),
    (∀ z : (A E)ˣ, η (ideleNorm F E z) = 1) → (∀ b φ v, (Om (nU b) φ).1 v = ψ (b * q4 D.δ v) * φ.1 v) →
    (∀ (a : (A F)ˣ) φ v, (Om (mD a) φ).1 v = ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i) →
    (∀ φ v, (Om (wW F) φ).1 v = ft4 D.δ φ.1 v) →
    (∀ h φ v, (L h φ).1 v = (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ v)) →
    ∀ h g, L h * Om g = Om (cD (nu F h) g) * L h := by
  intro F E _ _ _ _ _ D η Om L hη hn hm hw hL h g
  obtain ⟨ρ, hρ, hq, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hg : g ∈ (⊤ : Subgroup (G1 F)) := trivial
  rw [← (UpperTheory.ConvolutionTheory.R2.gen F).1] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | hx
    · apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext v
      rw [Module.End.mul_apply, Module.End.mul_apply, hL, hn, diagonalConj_unipotent, hn, hL]
      have hqv : q4 D.δ (D.act h⁻¹ v) = (((nu F h)⁻¹ : (A F)ˣ) : A F) * q4 D.δ v := by
        rw [hq, similitude_inv]
      rw [hqv, ← mul_assoc b]
      ring
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext v
      rw [Module.End.mul_apply, Module.End.mul_apply, hL, hw, diagonalConj_weyl, map_mul, Module.End.mul_apply, hm, hw]
      have hLf : (L h φ).1 = fun y => (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ y) := funext (hL h φ)
      rw [hLf, quaternaryFourier_const_mul, UpperTheory.ConvolutionTheory.R2.D.ftAct F E D h φ]
      have hlin : (fun i => (nu F h : A F) * D.act h⁻¹ (fun i => (((nu F h)⁻¹ : (A F)ˣ) : A F) * v i) i) = D.act h⁻¹ v := by
        funext i
        rw [hρ, hρ]
        have hs : (fun i => (((nu F h)⁻¹ : (A F)ˣ) : A F) * v i) = (((nu F h)⁻¹ : (A F)ˣ) : A F) • v := rfl
        rw [hs, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]
      have hη1 : η (nu F h)⁻¹ = 1 := by
        rw [map_inv]
        have : η (nu F h) = 1 := hη _
        rw [this, inv_one]
      rw [hlin, hη1, idelicNorm_inv]
      have ha : ((ab (nu F h) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (idelicNorm_pos (nu F h)).ne'
      push_cast
      field_simp
  | one => simp [diagonalConj_one]
  | mul x y _ _ hx hy =>
    rw [map_mul, diagonalConj_mul, map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ hx =>
    have e1 : Om x * Om x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have cinv : cD (nu F h) x⁻¹ * cD (nu F h) x = 1 := by
      rw [← diagonalConj_mul, inv_mul_cancel, diagonalConj_one]
    have e2 : Om (cD (nu F h) x⁻¹) * Om (cD (nu F h) x) = 1 := by rw [← map_mul, cinv, map_one]
    calc L h * Om x⁻¹ = (Om (cD (nu F h) x⁻¹) * Om (cD (nu F h) x)) * (L h * Om x⁻¹) := by rw [e2, one_mul]
      _ = Om (cD (nu F h) x⁻¹) * ((Om (cD (nu F h) x) * L h) * Om x⁻¹) := by simp only [mul_assoc]
      _ = Om (cD (nu F h) x⁻¹) * (L h * (Om x * Om x⁻¹)) := by rw [← hx]; simp only [mul_assoc]
      _ = Om (cD (nu F h) x⁻¹) * L h := by rw [e1, mul_one]
