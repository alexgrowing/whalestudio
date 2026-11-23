import Mathlib

open TensorProduct Module

namespace UpperTheory.V.Loc.R0

variable {Q E F B H : Type} [Field Q] [Field E] [Algebra Q E] [Field F] [Algebra Q F]
  [CommRing B] [Algebra Q B] [Algebra F B] [IsScalarTower Q F B]

theorem inv_tensor [FiniteDimensional Q E] (a : H → B ≃ₐ[Q] B)
    (ha : ∀ b, (∀ g, a g b = b) → ∃ c : F, algebraMap F B c = b) (z : E ⊗[Q] B)
    (hz : ∀ g, (a g).toLinearMap.lTensor E z = z) :
    ∃ c : E ⊗[Q] F, (IsScalarTower.toAlgHom Q F B).toLinearMap.lTensor E c = z := by
  let b := Module.finBasis Q E
  let φ : Fin (finrank Q E) → E ⊗[Q] B →ₗ[Q] B := fun i =>
    (TensorProduct.lid Q B).toLinearMap ∘ₗ (b.coord i).rTensor B
  have h1 : ∀ y : E ⊗[Q] B, ∑ i, b i ⊗ₜ[Q] φ i y = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e c =>
      conv_rhs => rw [← b.sum_repr e, sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, smul_tmul]
    | add x y hx hy => simp only [map_add, tmul_add, Finset.sum_add_distrib, hx, hy]
  have h2 : ∀ g i (y : E ⊗[Q] B), φ i ((a g).toLinearMap.lTensor E y) = a g (φ i y) := by
    intro g i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e c => simp [φ]
    | add x y hx hy => simp only [map_add, hx, hy]
  choose c hc using fun i => ha (φ i z) fun g => by rw [← h2, hz]
  refine ⟨∑ i, b i ⊗ₜ[Q] c i, ?_⟩
  rw [← h1 z, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc]
  rfl

theorem basis_of_unit [FiniteDimensional Q E] [Nontrivial B] (a : H → B ≃ₐ[Q] B)
    (ha : ∀ b, (∀ g, a g b = b) → ∃ c : F, algebraMap F B c = b) (κ : H → E)
    (T : H → E ⊗[Q] B →ₗ[E] E ⊗[Q] B) (hT : ∀ g v b, T g (v ⊗ₜ[Q] b) = (κ g * v) ⊗ₜ[Q] a g b)
    (S : E ⊗[Q] F →ₗ[Q] Module.End Q (E ⊗[Q] B))
    (hS : ∀ e f v b, S (e ⊗ₜ[Q] f) (v ⊗ₜ[Q] b) = (e • v) ⊗ₜ[Q] (f • b))
    (x : E ⊗[Q] B) (hu : IsUnit x) (hx : ∀ g, T g x = x) (y : E ⊗[Q] B) (hy : ∀ g, T g y = y) :
    ∃! c : E ⊗[Q] F, y = S c x := by
  let j := (IsScalarTower.toAlgHom Q F B).toLinearMap.lTensor E
  have hj : Function.Injective j :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap F B).injective
  have h1 : ∀ c z, S c z = j c * z := by
    intro c z
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, LinearMap.add_apply, hc, hc', add_mul]
    | tmul e f =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz', mul_add]
      | tmul v b => simp [hS, j, Algebra.smul_def]
  have h2 : ∀ g z w, T g (z * w) = (a g).toLinearMap.lTensor E z * T g w := by
    intro g z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, hc, hc', add_mul]
    | tmul e f =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz', mul_add]
      | tmul v b => simp [hT, mul_left_comm]
  obtain ⟨z, rfl⟩ : ∃ z, y = z * x := ⟨y * ↑hu.unit⁻¹, by simp [mul_assoc]⟩
  obtain ⟨c, hc⟩ := inv_tensor a ha z fun g => hu.mul_right_cancel (by
    have := hy g
    rwa [h2, hx] at this)
  refine ⟨c, by simp only [h1]; rw [← hc], fun c' hc' => hj ?_⟩
  simp only [h1] at hc'
  rw [← hu.mul_right_cancel hc']
  exact hc.symm

theorem unit_of_span (D : Submodule E (E ⊗[Q] B)) (hD : finrank E D = 1) {m : ℕ} (b : Fin m → B)
    (d : Fin m → E ⊗[Q] B) (hd : ∀ i, d i ∈ D)
    (h : (1 : E ⊗[Q] B) = ∑ i, AlgebraTensorModule.map (LinearMap.id : E →ₗ[E] E) (LinearMap.mulLeft Q (b i)) (d i)) :
    ∃ x ∈ D, IsUnit x := by
  obtain ⟨x, -, hx⟩ := finrank_eq_one_iff'.1 hD
  choose e he using fun i => hx ⟨d i, hd i⟩
  have h1 : ∀ c (z : E ⊗[Q] B), AlgebraTensorModule.map (LinearMap.id : E →ₗ[E] E) (LinearMap.mulLeft Q c) z =
      ((1 : E) ⊗ₜ[Q] c) * z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz', mul_add]
    | tmul v b => simp
  refine ⟨x, x.2, IsUnit.of_mul_eq_one (∑ i, e i • ((1 : E) ⊗ₜ[Q] b i)) ?_⟩
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : d i = e i • (x : E ⊗[Q] B) := (congrArg Subtype.val (he i)).symm
  rw [h1, this, mul_smul_comm, mul_smul_comm, mul_comm]

end UpperTheory.V.Loc.R0
