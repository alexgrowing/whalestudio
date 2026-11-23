import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DifferentiableHf

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem vacuum_at_zero_mul_compact (m : ℕ) (e : ℤ) (x : M2 n) {k : M2 n} (hk : InK k) :
    fz m e 0 (x * k) = fz m e 0 x * fz m e 0 k := by
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  rw [first_cayley_block_mul_compact x hk, Matrix.det_mul, Matrix.det_mul, mul_zpow, mul_zpow]
  ring

theorem norm_fz0K (m : ℕ) (e : ℤ) {k : M2 n} (hk : InK k) : star (fz m e 0 k) * fz m e 0 k = 1 := by
  have hk1 : Complex.normSq (det k) = 1 := by
    have h := congrArg Matrix.det hk.2
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      mul_comm, Complex.mul_conj] at h
    exact_mod_cast h
  have hu := normSq_det_u1K hk
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  unfold fz
  simp only [neg_zero, Complex.cpow_zero, mul_one, map_mul, map_zpow₀, hk1, hu, _root_.one_zpow]
  simp

theorem first_cayley_block_one : u1 (1 : M2 n) = 1 := by
  unfold u1
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp
theorem second_cayley_block_one : u2 (1 : M2 n) = 1 := by
  unfold u2
  rw [← Matrix.fromBlocks_one, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  simp

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)

include hK in
theorem ιK (k : Kg) : InK (ι k) := (hK _).mpr ⟨k, rfl⟩

theorem ι_inv (k : Kg) : ι k⁻¹ = (ι k)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, inv_mul_cancel, map_one]

include hK in
theorem first_cayley_block_inv (k : Kg) : u1 (ι k⁻¹) = (u1 (ι k))⁻¹ := by
  have h : u1 (ι k⁻¹) * u1 (ι k) = 1 := by
    rw [← first_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, first_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem second_cayley_block_inv (k : Kg) : u2 (ι k⁻¹) = (u2 (ι k))⁻¹ := by
  have h : u2 (ι k⁻¹) * u2 (ι k) = 1 := by
    rw [← second_cayley_block_mul_compact _ (ιK ι hK k), ← map_mul, inv_mul_cancel, map_one, second_cayley_block_one]
  exact (Matrix.inv_eq_left_inv h).symm

include hK in
theorem vacuum_at_zero_inv_star (m : ℕ) (e : ℤ) (k : Kg) : fz m e 0 (ι k⁻¹) = star (fz m e 0 (ι k)) := by
  have hk := ιK ι hK k
  have h1 : fz m e 0 (ι k⁻¹) * fz m e 0 (ι k) = 1 := by
    rw [← vacuum_at_zero_mul_compact m e _ hk, ← map_mul, inv_mul_cancel, map_one]
    unfold fz
    simp [first_cayley_block_one]
  have h2 := norm_fz0K m e hk
  have hne : fz m e 0 (ι k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

include hK in
theorem rho_shift (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (k1 k : Kg) :
    rhoP ι m e Y (k1⁻¹ * k) = fz m e 0 (ι k1) * rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) k := by
  have ha := ιK ι hK k1
  have hb := ιK ι hK k
  have hdet : IsUnit (u2 (ι k1)).det := Matrix.isUnit_det_of_left_inverse (second_cayley_block_compact_unitary ha)
  unfold rhoP
  rw [map_mul, vacuum_at_zero_mul_compact m e _ hb, vacuum_at_zero_inv_star ι hK m e k1, second_cayley_block_mul_compact _ hb, first_cayley_block_mul_compact _ hb,
    second_cayley_block_inv ι hK k1, first_cayley_block_inv ι hK k1, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdet]
  simp only [star_mul', star_star, Matrix.mul_assoc]
  ring

theorem Hf_up (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p y : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (hy : InG y) (z : ℂ) :
    Hf m e ψ a b z (p * y) = lam m e z p * Hf m e ψ a b z y := by
  simp only [Hf]
  rw [← integral_const_mul]
  congr 1; funext t
  rw [show p * y * a * nU (herm t) * b = p * (y * a * nU (herm t) * b) by simp only [Matrix.mul_assoc],
    fz_up hp hp21 (inG_path hy ha hb t)]
  ring

include hK in

theorem tOp_formula (m : ℕ) (e : ℤ) (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b p : M2 n} (ha : InG a) (hb : InG b)
    (hp : InG p) (hp21 : p.toBlocks₂₁ = 0) (k1 : Kg) (Y : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) (p * ι k1) =
      lam m e z p * fz m e 0 (ι k1) * tOp μ ι (rhoP ι m e (u2 (ι k1) * Y * (u1 (ι k1))⁻¹)) ψ a b (fz m e z) 1 := by
  unfold tOp
  have hs := integral_mul_left_eq_self (μ := μ) (fun k => rhoP ι m e Y k *
    ∫ t, fz m e z (p * ι k1 * ι k * a * nU (herm t) * b) * ψ t) k1⁻¹
  rw [← hs, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext k
  have hι : ι k1 * ι (k1⁻¹ * k) = ι k := by
    rw [← map_mul, mul_inv_cancel_left]
  have hH := Hf_up m e ψ ha hb hp hp21 (ιK ι hK k).1 z
  unfold Hf at hH
  rw [rho_shift ι hK m e Y k1 k, Matrix.mul_assoc p (ι k1), hι, hH]
  simp only [Matrix.one_mul]
  ring

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
