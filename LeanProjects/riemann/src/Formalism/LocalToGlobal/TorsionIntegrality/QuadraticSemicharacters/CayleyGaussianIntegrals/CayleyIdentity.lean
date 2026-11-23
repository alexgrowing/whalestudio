import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Diag

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[reducible] def coreOf (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) : InnerProductSpace.Core ℂ V where
  inner x y := H y x
  conj_inner_symm x y := (hH x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hP x h).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    have := hP x h
    rw [hx] at this
    simp at this

theorem symm_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, H (T x) y = H x (T y)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : Fin (Module.finrank ℂ V) → ℝ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, T (b i) = (t i : ℂ) • b i := by
  letI cd : InnerProductSpace.Core ℂ V := coreOf H hH hP
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ V := ‹FiniteDimensional ℂ V›
  have hS : LinearMap.IsSymmetric T := fun x y => (hT y x).symm
  let b := hS.eigenvectorBasis rfl
  refine ⟨b.toBasis, fun i => hS.eigenvalues rfl i, ?_, ?_⟩
  · intro i j
    rw [OrthonormalBasis.coe_toBasis]
    have h := (orthonormal_iff_ite.mp b.orthonormal) j i
    exact h.trans (if_congr eq_comm rfl rfl)
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
    exact hS.apply_eigenvectorBasis rfl i

theorem cayley_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (Ae : V ≃ₗ[ℂ] V)
    (hA : ∀ u v, H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re := by
  set B : V →ₗ[ℂ] V := (Ae.symm : V ≃ₗ[ℂ] V).toLinearMap with hBdef
  have key : ∀ x y, H (B x) y + H x (B y) = H x y := by
    intro x y
    have h := hA (Ae.symm x) (Ae.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    simpa [hBdef, add_comm] using h
  set T : V →ₗ[ℂ] V := Complex.I • ((2 : ℂ) • B - LinearMap.id) with hTdef
  have hTx : ∀ x, T x = Complex.I • ((2 : ℂ) • B x - x) := by
    intro x; simp [hTdef]
  have hT : ∀ x y, H (T x) y = H x (T y) := by
    intro x y
    rw [hTx, hTx]
    simp only [map_smul, map_sub, map_smulₛₗ, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,
      Complex.conj_I, RingHom.id_apply, map_ofNat]
    linear_combination (2 * Complex.I) * key x y
  obtain ⟨b, t, hb, hbt⟩ := symm_diag H hH hP T hT
  have hne : ∀ i, (1 - Complex.I * (t i : ℂ)) ≠ 0 := by
    intro i h
    have := congrArg Complex.re h
    simp at this
  refine ⟨b, fun i => 2 / (1 - Complex.I * (t i : ℂ)), hb, ?_, ?_⟩
  · intro i
    have h1 := hbt i
    rw [hTx] at h1
    have hw : B (b i) = ((1 - Complex.I * (t i : ℂ)) / 2) • b i := by
      linear_combination (norm := skip) (-Complex.I / 2) • h1
      match_scalars <;> (ring_nf; simp only [Complex.I_sq]; ring)
    apply Ae.symm.injective
    have hB' : Ae.symm (b i) = B (b i) := rfl
    rw [LinearEquiv.symm_apply_apply, map_smul, hB', hw, smul_smul,
      show 2 / (1 - Complex.I * (t i : ℂ)) * ((1 - Complex.I * (t i : ℂ)) / 2) = 1 by
        field_simp [hne i], one_smul]
  · intro i
    have hre : (1 - Complex.I * (t i : ℂ)).re = 1 := by simp
    have him : (1 - Complex.I * (t i : ℂ)).im = -t i := by simp
    have hns : Complex.normSq (1 - Complex.I * (t i : ℂ)) = 1 + t i ^ 2 := by
      rw [Complex.normSq_apply, hre, him]; ring
    have h2r : (2 : ℂ).re = 2 := by norm_num
    have h2i : (2 : ℂ).im = 0 := by norm_num
    rw [Complex.div_re, hre, him, hns, h2r, h2i, zero_mul, zero_div, add_zero, mul_one]
    positivity

theorem cayley_identity (H : Sesq V) (δ Ae : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V))
    (hAe : ∀ x, Ae x = x - δ.symm x) (u v : V) : H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v) := by
  have key : H (δ.symm u) (δ.symm v) = H u v := by
    have h := hδ (δ.symm u) (δ.symm v)
    simpa using h.symm
  simp only [hAe, map_sub, LinearMap.sub_apply]
  rw [key]
  ring

theorem unitary_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (δ Ae : V ≃ₗ[ℂ] V)
    (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hAe : ∀ x, Ae x = x - δ.symm x) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re :=
  cayley_diag H hH hP Ae (cayley_identity H δ Ae hδ hAe)

theorem det_of_diag {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n ℂ V) (l : n → ℂ) (L : V →ₗ[ℂ] V)
    (hL : ∀ i, L (b i) = l i • b i) : LinearMap.det L = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b L = Matrix.diagonal l := by
    ext i j
    rw [LinearMap.toMatrix_apply, hL, map_smul, b.repr_self, Finsupp.smul_apply]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Matrix.diagonal_apply, Finsupp.single_apply, h, h.symm]
  rw [hM, Matrix.det_diagonal]

theorem form_of_diag {n : Type*} [Fintype n] [DecidableEq n] (H : Sesq V) (b : Module.Basis n ℂ V) (l : n → ℂ)
    (L : V →ₗ[ℂ] V) (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (hL : ∀ i, L (b i) = l i • b i)
    (w : n → ℂ) :
    H (L (b.equivFun.symm w)) (b.equivFun.symm w) = ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2 := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, hL, smul_smul, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, map_smulₛₗ, hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Complex.mul_conj (w i)
  rw [Complex.normSq_eq_norm_sq] at h
  push_cast at h
  linear_combination (l i) * h

end Diag

end Formalism.L2.Th1.H
