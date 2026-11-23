import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open UpperTheory.ConvolutionTheory.RankTwoDescent

open GroundTheory.Automorphic.FourierWhittaker (vecLattice mem_vecLattice)

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

variable {E : Type} [Field E] [NumberField E]

theorem em_aE (a : (A ℚ)ˣ) : em E (aE a) = aE (ideleEmbedding ℚ E a) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [em]

theorem psi_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]

theorem psi_rt (k : ℚ) : ψ (rt k) = 1 := by simp [ψ, adelicChar_algebraMap]

theorem psi_neg_mul (x : A ℚ) : ψ (-x) * ψ x = 1 := by
  rw [← psi_add, neg_add_cancel]
  simpa using psi_rt (0 : ℚ)

theorem n_add (x y : A E) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  rw [nU_add, gl_mul]

theorem mkE_add (D : Dat ℚ E) (a b c d : A ℚ) : D.mkE (a + c) (b + d) = D.mkE a b + D.mkE c d := by
  simp only [Dat.mkE, map_add, add_mul]
  abel

theorem mkE_rat (D : Dat ℚ E) (x y : ℚ) :
    D.mkE (rt x) (rt y) = rt (algebraMap ℚ E x + algebraMap ℚ E y * D.θ) := by
  simp only [Dat.mkE, UpperTheory.ConvolutionTheory.R2.rt, AdeleBaseChange.adeleMap_algebraMap, map_add, map_mul]

theorem nE_add (D : Dat ℚ E) (x c : Fin 2 → A ℚ) : nE D (x + c) = nE D x * nE D c := by
  simp only [nE, Pi.add_apply, mkE_add, n_add]

theorem rat_n (k : E) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap E (A E) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp

theorem Wo_right (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ) (x h : GL (Fin 2) (A E)) :
    Wo D (fun g => φ (g * x)) h = Wo D φ (h * x) := by
  simp only [Wo, mul_assoc]

theorem Wo_shift (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, φ (ratGL E 2 γ * g) = φ g)
    (c : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)) :
    Wo D φ (nE D c * h) = ψ (-(c 1)) * Wo D φ h := by
  let J : (Fin 2 → A ℚ) → ℂ := fun x => φ (nE D x * h) * ψ (x 1)
  have hper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ x, J (ξ + x) = J x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    obtain ⟨γ, hγ⟩ := rat_n (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ)
    have e1 : nE D ((fun i => algebraMap ℚ (A ℚ) (η i)) + x) = ratGL E 2 γ * nE D x := by
      rw [nE_add, hγ, ← mkE_rat]
      rfl
    simp only [J]
    rw [e1, mul_assoc, hL]
    change _ * ψ (rt (η 1) + x 1) = _
    rw [psi_add, psi_rt, one_mul]
  have hs := GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add c hper
  have e : ∀ u : Fin 2 → A ℚ, φ (nE D u * (nE D c * h)) * ψ (u 1) = ψ (-(c 1)) * J (u + c) := by
    intro u
    simp only [J, Pi.add_apply, nE_add, mul_assoc]
    rw [psi_add]
    have := psi_neg_mul (c 1)
    linear_combination (-(φ (nE D u * (nE D c * h))) * ψ (u 1)) * this
  unfold Wo
  simp_rw [e]
  rw [integral_const_mul]
  congr 1

theorem pInf_sInf (x : TR.Rinf ℚ) : TR.pInf ℚ (TR.sInf ℚ x) = x := (TR.infEq ℚ).symm_apply_apply x

def bI (u : ℝ) : A ℚ := TR.sInf ℚ fun _ => u

theorem bI_snd (u : ℝ) : (bI u).2 = 0 := rfl

theorem psi_bI (v : ℝ) : ψ (-(bI v)) = Complex.exp (2 * Real.pi * Complex.I * (v : ℂ)) := by
  obtain ⟨-, h⟩ := UpperTheory.ConvolutionTheory.R2.C.splitA ℚ
  rw [h]
  have h2 : (-(bI v)).2 = 0 := by
    change -(bI v).2 = 0
    rw [bI_snd, neg_zero]
  have h3 : ∀ w, TR.pInf ℚ (-(bI v)) w = -v := by
    intro w
    rw [map_neg, bI, pInf_sInf]
    rfl
  simp only [h2, h3, AddChar.map_zero_eq_one, Fintype.prod_subsingleton _ Rat.infinitePlace]
  simp

theorem iy_coe {y : ℝ} (h : y ≠ 0) : ((iy y : (A ℚ)ˣ) : A ℚ) = 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => y := by
  rw [iy, dif_neg h]
  rfl

theorem iy_inv_coe {y : ℝ} (h : y ≠ 0) : (((iy y)⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 - TR.sInf ℚ 1 + TR.sInf ℚ fun _ => y⁻¹ := by
  rw [iy, dif_neg h]
  rfl

theorem iy_one : iy 1 = 1 := by
  refine Units.ext ?_
  rw [iy_coe one_ne_zero]
  have : (fun _ : InfinitePlace ℚ => (1 : ℝ)) = 1 := rfl
  simp [this]

theorem re_iy {y : ℝ} (h : y ≠ 0) : re (iy y : A ℚ) = y := by
  rw [re, iy_coe h, map_add, map_sub, pInf_sInf, pInf_sInf, map_one]
  simp

theorem iy_mul_bI {y : ℝ} (h : y ≠ 0) (u : ℝ) : (iy y : A ℚ) * bI u = bI (y * u) := by
  rw [iy_coe h, bI, bI, add_mul, sub_mul, one_mul, ← map_mul, ← map_mul]
  have h1 : (1 * fun _ : InfinitePlace ℚ => u) = fun _ : InfinitePlace ℚ => u := one_mul _
  have h2 : ((fun _ : InfinitePlace ℚ => y) * fun _ : InfinitePlace ℚ => u) = fun _ : InfinitePlace ℚ => y * u := rfl
  rw [h1, h2]
  simp

def hU (D : Dat ℚ E) (u : ℝ) : GL (Fin 2) (A E) := nE D ![0, bI u]

theorem em_conj (D : Dat ℚ E) (a : (A ℚ)ˣ) (b : A ℚ) :
    em E (aE a) * nE D ![0, b] = nE D ![0, (a : A ℚ) * b] * em E (aE a) := by
  rw [em_aE]
  simp only [nE, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [aE_mul_nU]
  congr 3
  simp only [Dat.mkE, map_zero, zero_add, map_mul, coe_ideleEmbedding, mul_assoc]

theorem Wo_hU (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hL : ∀ γ g, φ (ratGL E 2 γ * g) = φ g) {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    Wo D (fun g => φ (g * hU D u)) (em E (aE (iy y))) =
      Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) * Wo D φ (em E (aE (iy y))) := by
  rw [Wo_right, hU, em_conj, iy_mul_bI hy, Wo_shift D hL]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [psi_bI]

def X (t : ℝ) : GL (Fin 2) (TR.Rinf ℚ) :=
  ⟨!![fun _ => Real.cos t, fun _ => -Real.sin t; fun _ => Real.sin t, fun _ => Real.cos t],
   !![fun _ => Real.cos t, fun _ => Real.sin t; fun _ => -Real.sin t, fun _ => Real.cos t],
   by ext i j w; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq t],
   by ext i j w; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq t]⟩

theorem rot_eq (t : ℝ) : rot t = TR.infGL ℚ 2 (X t) := by
  rw [rot]
  congr 1
  refine Units.ext ?_
  rfl

theorem X_zero : X 0 = 1 := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [X]

theorem X_neg (t : ℝ) : X (-t) = (X t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq t]

theorem X_add_pi (t : ℝ) : X (t + Real.pi) = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) * X t := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add_pi, Real.sin_add_pi]

theorem rot_zero : rot 0 = 1 := by rw [rot_eq, X_zero, map_one]

theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

theorem rot_add_pi (t : ℝ) : rot (t + Real.pi) = Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId ℚ (-1)) * rot t := by
  rw [rot_eq, rot_eq, X_add_pi, map_mul]
  congr 1
  exact corner_sc _ _

theorem em_scalar (z : (A ℚ)ˣ) :
    em E (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E z) := by
  refine Units.ext ?_
  ext i j
  by_cases e : i = j <;> simp [em, e, Matrix.scalar_apply, Matrix.diagonal]

theorem ideleNorm_embedding_neg_one_real (D : Dat ℚ E) : ideleNorm ℚ E (ideleEmbedding ℚ E (TR.infId ℚ (-1))) = 1 := by
  rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin, ← map_pow]
  simp

theorem Wo_rot_pi [IsTotallyComplex E] (D : Dat ℚ E) (ω : HChar ℚ) {φ : GL (Fin 2) (A E) → ℂ}
    (hc : ∀ z g, φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * φ g) (a : (A ℚ)ˣ) (t : ℝ) :
    Wo D φ (em E (aE a * rot (t + Real.pi))) = Wo D φ (em E (aE a * rot t)) := by
  have e : em E (aE a * rot (t + Real.pi)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E (TR.infId ℚ (-1))) * em E (aE a * rot t) := by
    rw [rot_add_pi, ← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc, map_mul, em_scalar]
  have h2 : ∀ (u : GL (Fin 2) (A E)) (g : GL (Fin 2) (A E)),
      φ (u * (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E (TR.infId ℚ (-1))) * g)) = φ (u * g) := by
    intro u g
    rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc, hc, ideleNorm_embedding_neg_one_real D]
    simp
  rw [e]
  simp only [Wo, h2]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Nz
