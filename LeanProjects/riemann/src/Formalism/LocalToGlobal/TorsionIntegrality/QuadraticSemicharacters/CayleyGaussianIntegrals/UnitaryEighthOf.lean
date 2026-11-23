import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.UnitaryConstant
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Cay

section Det

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem gram_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (H : Sesq V) (hpos : IsPosDef H)
    (e : Module.Basis ι ℂ V) : (Matrix.of fun i j => H (e i) (e j)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hHw : H (∑ i, v i • e i) = 0 := by
    apply e.ext
    intro j
    have h := congrFun hM j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    exact h
  have hw0 : (∑ i, v i • e i) ≠ 0 := by
    intro h0
    exact hv (funext fun i => Fintype.linearIndependent_iff.1 e.linearIndependent v h0 i)
  have h := hpos _ hw0
  rw [hHw, LinearMap.zero_apply, Complex.zero_re] at h
  exact lt_irrefl _ h

theorem det_adj (H : Sesq V) (hpos : IsPosDef H) (f f' : V →ₗ[ℂ] V) (h : ∀ x y, H (f x) y = H x (f' y)) :
    LinearMap.det f = conj (LinearMap.det f') := by
  classical
  let e := Module.finBasis ℂ V
  have hG := gram_det_ne_zero H hpos e
  have hfe : ∀ (g : V →ₗ[ℂ] V) j, g (e j) = ∑ k, LinearMap.toMatrix e e g k j • e k := fun g j => by
    simp only [LinearMap.toMatrix_apply]; exact (e.sum_repr (g (e j))).symm
  have hmat : (LinearMap.toMatrix e e f).transpose * (Matrix.of fun i j => H (e i) (e j))
      = (Matrix.of fun i j => H (e i) (e j)) * (LinearMap.toMatrix e e f').map (starRingEnd ℂ) := by
    ext i j
    have h1 := h (e i) (e j)
    rw [hfe f i, hfe f' j] at h1
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply]
    exact h1.trans (Finset.sum_congr rfl fun k _ => mul_comm _ _)
  have hc : ((LinearMap.toMatrix e e f').map (starRingEnd ℂ)).det
      = starRingEnd ℂ (LinearMap.toMatrix e e f').det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc] at hdet
  rw [← LinearMap.det_toMatrix e f, ← LinearMap.det_toMatrix e f']
  exact mul_right_cancel₀ hG (hdet.trans (mul_comm _ _))

end Det

end Cay

theorem cayleyDet : DetCayley := by
  intro V _ _ _ H hH hpos δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  have hadj : ∀ x y, H ((Ae : V →ₗ[ℂ] V) x) y = H x (((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) y) := by
    intro x y
    obtain ⟨x, rfl⟩ : ∃ x', x = δ x' := ⟨δ.symm x, by simp⟩
    simp only [LinearEquiv.coe_coe, hA, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hi]
  have h1 := Cay.det_adj H hpos _ _ hadj
  have h2 : ((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) = ((-1 : ℂ) • (δ : V →ₗ[ℂ] V)) ∘ₗ (Ae : V →ₗ[ℂ] V) := by
    ext x
    simp [hA]
  conv_lhs => rw [h1, Complex.conj_conj, h2, LinearMap.det_comp, LinearMap.det_smul]

namespace Cay

theorem selfDual_img {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (Λ : AddSubgroup V)
    (δ : V ≃ₗ[ℂ] V) (hδ : IsIsom H H (δ : V →ₗ[ℂ] V)) (hΛ : IsSelfDual H Λ) :
    IsSelfDual H (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hδ a b
  unfold IsSelfDual at hΛ ⊢
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H x y = m := hx
    rw [imgLat, AddSubgroup.mem_map]
    refine ⟨δ.symm x, ?_, by simp⟩
    rw [← hΛ]
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H (δ.symm x) y = m
    intro y hy
    obtain ⟨m, hm⟩ := hx' (δ y) (by rw [imgLat, AddSubgroup.mem_map]; exact ⟨y, hy, rfl⟩)
    refine ⟨m, ?_⟩
    have e := hi (δ.symm x) y
    rw [LinearEquiv.apply_symm_apply] at e
    show (H (δ.symm x) y).im = m
    rw [← e]; exact hm
  · intro hx
    rw [imgLat, AddSubgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← hΛ] at ha
    have ha' : ∀ y ∈ Λ, ∃ m : ℤ, altE H a y = m := ha
    show ∀ y ∈ imgLat (δ : V →ₗ[ℂ] V) Λ, ∃ m : ℤ, altE H (δ a) y = m
    intro y hy
    rw [imgLat, AddSubgroup.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    obtain ⟨m, hm⟩ := ha' b hb
    refine ⟨m, ?_⟩
    show (H (δ a) (δ b)).im = m
    rw [hi]; exact hm

end Cay

theorem UnitaryEighth_of (hC : UnitaryConstant) (hG : UnitaryGauss) (hI : UnitaryIndex) : UnitaryEighth := by
  intro V _ _ _ H Λ α δ Ae hL hU hAML θ hθ hθ0 c hc
  have hd : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  obtain ⟨_, hidx⟩ := hI V H Λ α δ Ae hL hU
  have hne : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
    exact mul_ne_zero h1 (pow_ne_zero _ (norm_ne_zero_iff.2 hd)) hidx.symm
  obtain ⟨S, hS⟩ := (cosetRepsExist V (latA Λ δ Ae) Λ hne).1
  have hc' := hC V H Λ α δ Ae hL hU hAML S hS θ hθ
  have hg := hG V H Λ α δ Ae hU S hS
  have hI0 : inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hc
    apply hθ0
    funext z
    have h1 := congrFun hc (δ z)
    simpa [pullInv] using h1
  have hceq : c = (‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)
      * gaussC H α Ae S := smul_left_injective ℂ hI0 (hc.symm.trans hc')
  have hdc := cayleyDet V H hU.herm hU.pos δ Ae hU.isom hU.cay
  rw [hceq, mul_pow, hg, mul_one, div_pow]
  generalize LinearMap.det (Ae : V →ₗ[ℂ] V) = d at *
  generalize LinearMap.det (δ : V →ₗ[ℂ] V) = D at *
  have hn2 : ((‖d‖ : ℝ) : ℂ) ^ 2 = d * conj d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hs : ((-1 : ℂ) ^ Module.finrank ℂ V) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show ((‖d‖ : ℝ) : ℂ) ^ 8 = (((‖d‖ : ℝ) : ℂ) ^ 2) ^ 4 by ring, hn2, hdc, div_eq_iff (pow_ne_zero _ hd)]
  linear_combination (D ^ 4 * d ^ 8) * hs

end Formalism.L2.Th1.H
