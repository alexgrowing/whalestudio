import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFDerivAtOfCompImmersion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetUnitaryMulMul

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem jac_exp_herm {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    (NormedSpace.exp (pY B))ᴴ = NormedSpace.exp (pY B) := by
  rw [← Matrix.exp_conjTranspose, pY_conjTranspose]

theorem jac_exp_two {p q : ℕ} (B : Fin p → Fin q → ℂ) :
    NormedSpace.exp (pY B + pY B) = NormedSpace.exp (pY B) * NormedSpace.exp (pY B) := Matrix.exp_add_of_commute _ _ (Commute.refl _)

theorem jac_cancel {p q : ℕ} (B : Fin p → Fin q → ℂ) (X Z : Mat p q)
    (h : NormedSpace.exp (pY B) * X * NormedSpace.exp (pY B)
      = NormedSpace.exp (pY B) * Z * NormedSpace.exp (pY B)) : X = Z := by
  have hu := Matrix.isUnit_exp (pY B)
  exact hu.mul_left_cancel (hu.mul_right_cancel h)

theorem jac_block {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (U : Matrix (Fin p) (Fin p) ℂ)
    (V : Matrix (Fin q) (Fin q) ℂ)
    (h : pY X = (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * pY Z * Matrix.fromBlocks U 0 0 V) :
    Matrix.of X = Uᴴ * Matrix.of Z * V := by
  have h1 := congrArg Matrix.toBlocks₁₂ h
  simpa [pY, pOf, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_assoc] using h1

noncomputable def jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ) :
    (m → n → ℂ) →ₗ[ℝ] (m → n → ℂ) where
  toFun Z := fun i j => (U * Matrix.of Z * V) i j
  map_add' Z W := by
    have : Matrix.of (Z + W) = Matrix.of Z + Matrix.of W := rfl
    rw [this, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' t Z := by
    have : Matrix.of (t • Z) = t • Matrix.of Z := rfl
    rw [this, Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem of_jacMul {m n : Type} [Fintype m] [Fintype n] (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (Z : m → n → ℂ) : Matrix.of (jacMul U V Z) = U * Matrix.of Z * V := rfl

private theorem pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ {E : Type*} [AddCommGroup E] [Module ℝ E] (X Z : E)
    (h : X + X = Z + Z) : X = Z := by
  have h2 : (2 : ℝ) • X = (2 : ℝ) • Z := by rw [two_smul, two_smul]; exact h
  have h3 := congrArg (fun W => (1 / 2 : ℝ) • W) h2
  simpa [smul_smul] using h3

private theorem pY_injective {p q : ℕ} (X Z : Fin p → Fin q → ℂ) (h : pY X = pY Z) : X = Z := by
  funext i j
  have h1 := congrFun (congrFun (congrArg Matrix.toBlocks₁₂ h) i) j
  simpa [pY, pOf] using h1

private theorem conjTranspose_mul_mul_mul_eq_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] (g E F k X : Matrix n n ℂ)
    (hE : Eᴴ = E) (hF : Fᴴ = F) (h : E * g = k * F) :
    gᴴ * (E * X * E) * g = F * (kᴴ * X * k) * F := by
  have h1 : gᴴ * E = (E * g)ᴴ := by rw [Matrix.conjTranspose_mul, hE]
  calc gᴴ * (E * X * E) * g = (gᴴ * E) * X * (E * g) := by simp only [Matrix.mul_assoc]
    _ = (k * F)ᴴ * X * (k * F) := by rw [h1, h]
    _ = F * (kᴴ * X * k) * F := by rw [Matrix.conjTranspose_mul, hF]; simp only [Matrix.mul_assoc]

private theorem fromBlocks_unitary_conjTranspose_mul_self {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (V : Matrix (Fin q) (Fin q) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin q) ℂ) :
    (Matrix.fromBlocks U 0 0 V)ᴴ * Matrix.fromBlocks U 0 0 V = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hU, hV]

private theorem injective_of_det_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (h : LinearMap.det f ≠ 0) : Function.Injective f :=
  (LinearMap.equivOfDetNeZero f h).injective

private theorem conjTranspose_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hU
  exact hU

theorem jacobian_action_p : ∀ (p q : ℕ) (g : Mat p q) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous ψ → (∀ B, ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, NormedSpace.exp (pY B) * g = Matrix.fromBlocks U 0 0 V * NormedSpace.exp (pY (ψ B))) → (∀ B : Fin p → Fin q → ℂ, 0 < LinearMap.det (sP (pY B))) → (∀ B C : Fin p → Fin q → ℂ, sAd (pY B) (pY C) = pY (sP (pY B) C)) → (∀ B : Fin p → Fin q → ℂ, ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B)) → ∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * LinearMap.det (sP (pY (ψ B))) = LinearMap.det (sP (pY B)) := by
  intro p q g ψ hψ hK hdet hsAd hdiff B
  obtain ⟨A, hA, hAeq⟩ := hdiff (ψ B)
  obtain ⟨A0, hA0, hA0eq⟩ := hdiff B
  obtain ⟨U, hU, V, hV, hUV⟩ := hK B
  set L := LinearMap.toContinuousLinearMap (jacMul gᴴ g) with hL
  have hLapp : ∀ M, Matrix.of (L M) = gᴴ * Matrix.of M * g := fun M => of_jacMul gᴴ g M

  have hcomp : (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y)) =
      fun y => L ((fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) y) := by
    funext y
    obtain ⟨U', hU', V', hV', hy⟩ := hK y
    have hmat : NormedSpace.exp (pY (ψ y) + pY (ψ y)) = gᴴ * NormedSpace.exp (pY y + pY y) * g := by
      have hs := conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ 1 (jac_exp_herm y) (jac_exp_herm (ψ y)) hy
      rw [Matrix.mul_one, Matrix.mul_one, fromBlocks_unitary_conjTranspose_mul_self U' V' hU' hV', Matrix.mul_one] at hs
      rw [jac_exp_two, jac_exp_two, hs]
    apply Matrix.of.injective
    rw [hLapp]
    exact hmat
  have hLd : HasFDerivAt (fun y => (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) (ψ y))
      (L.comp A0) B := by
    rw [hcomp]
    exact L.hasFDerivAt.comp B hA0.hasFDerivAt
  have hinj : Function.Injective A := by
    intro C1 C2 h
    have h1 : Matrix.of (A C1) = Matrix.of (A C2) := by rw [h]
    rw [hAeq, hAeq] at h1
    have h2 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h2
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ (injective_of_det_ne_zero _ (hdet (ψ B)).ne' (pY_injective _ _ h2))
  obtain ⟨P, hP, hPA⟩ := GlobalTheory.hasFDerivAt_of_comp_immersion (Fin p → Fin q → ℂ) (Ix p q → Ix p q → ℂ)
    (fun C (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) ψ B A (L.comp A0) hA hinj
    hψ.continuousAt hLd
  refine ⟨P, hP, ?_⟩

  have hkey : ∀ C, sP (pY (ψ B)) (P C) = jacMul Uᴴ V (sP (pY B) C) := by
    intro C
    have h1 := congrArg (fun T : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ) => Matrix.of (T C)) hPA
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [hLapp, hAeq, hA0eq, conjTranspose_mul_mul_mul_eq_of_mul_eq g _ _ _ _ (jac_exp_herm B) (jac_exp_herm (ψ B)) hUV] at h1
    have h3 := jac_cancel (ψ B) _ _ h1
    rw [← pY_add, ← pY_add, hsAd, hsAd] at h3
    have h4 := jac_block _ _ U V h3
    rw [← of_jacMul] at h4
    have h5 := Matrix.of.injective h4
    simp only [map_add] at h5
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ _ _ h5
  have hlin : (sP (pY (ψ B))).comp (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ)) =
      (jacMul Uᴴ V).comp (sP (pY B)) := LinearMap.ext hkey
  have hd := congrArg (fun T => |LinearMap.det T|) hlin
  simp only [LinearMap.det_comp, abs_mul] at hd
  rw [abs_det_unitary_mul_mul p q Uᴴ (conjTranspose_mem_unitaryGroup hU) V hV _ (of_jacMul Uᴴ V), one_mul,
    abs_of_pos (hdet (ψ B)), abs_of_pos (hdet B)] at hd
  show |LinearMap.det (P : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ))| * _ = _
  rw [mul_comm]
  exact hd

end GlobalTheory.PolarU
