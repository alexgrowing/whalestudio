import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieListProducts

theorem alg_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂ) (A₁ A₂ : M) :
    (a • A₁ - b • A₂) + Complex.I • (a • A₂ + b • A₁) = (a + b * Complex.I) • (A₁ + Complex.I • A₂) := by
  have h : Complex.I • Complex.I • A₂ = -A₂ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [smul_add, add_smul, mul_smul, h]
  module

theorem alg_bracket {R : Type*} [Ring R] [Algebra ℂ R] (A₁ A₂ B₁ B₂ : R) :
    (A₁ + Complex.I • A₂) * (B₁ + Complex.I • B₂) - (B₁ + Complex.I • B₂) * (A₁ + Complex.I • A₂) =
      ((A₁ * B₁ - B₁ * A₁) - (A₂ * B₂ - B₂ * A₂)) + Complex.I • ((A₁ * B₂ - B₂ * A₁) + (A₂ * B₁ - B₁ * A₂)) := by
  have h : ∀ x : R, Complex.I • Complex.I • x = -x := fun x => by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h]
  module

section Lie

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem lie_zero : InLieW k r z 0 := by
  refine ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩

theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 := hX.1.1
    have h2 := hY.1.1
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).1, (hY.1.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).2, (hY.1.2 a ha).2, add_zero]
  · rw [Matrix.add_mulVec, hX.2, hY.2, add_zero]

theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    rw [this, ← smul_add, hX.1.1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).2, smul_zero]
  · rw [Matrix.smul_mulVec, hX.2, smul_zero]

theorem lie_sub {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X - Y) := by
  have := lie_add hX (lie_smul hY (-1))
  simpa [sub_eq_add_neg] using this

theorem conj_lie {X : Mx k r} (hX : InLieW k r z X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have h : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1.1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

theorem hpart1_lie {X : Mx k r} (hX : InLieW k r z X) : hpart1 (Hpk k r) X = X := by
  unfold hpart1
  rw [conj_lie hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_lie {X : Mx k r} (hX : InLieW k r z X) : hpart2 (Hpk k r) X = 0 := by
  unfold hpart2
  rw [conj_lie hX, add_neg_cancel, smul_zero]

theorem hpart1_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart1 (Hpk k r) (X₁ + Complex.I • X₂) = X₁ := by
  rw [CapelliCoordinates.hpart1_add, CapelliCoordinates.hpart1_smul, hpart1_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hpart2_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart2 (Hpk k r) (X₁ + Complex.I • X₂) = X₂ := by
  rw [CapelliCoordinates.hpart2_add, CapelliCoordinates.hpart2_smul, hpart2_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hsum (Z : Mx k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp [Complex.I_ne_zero]
  rw [e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem gl_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    InGlW k r z (X₁ + Complex.I • X₂) := by
  unfold InGlW
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]
  exact ⟨h1, h2⟩

theorem ec_comb {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (π : Mx k r → (W →L[ℂ] W))
    {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    ecOp π (X₁ + Complex.I • X₂) = dOp π X₁ + Complex.I • dOp π X₂ := by
  unfold ecOp
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]

end Lie

end LieListProducts

open LieListProducts in
theorem qr_ecLie_of : Qr.DOpLin → Qr.DOpBracket → Qr.EcLie := by
  intro hLin hBr W _ _ _ k r z π hπ Z Z' hZ hZ'
  obtain ⟨hX₁, hX₂⟩ := hZ
  obtain ⟨hY₁, hY₂⟩ := hZ'
  have eZ := hsum Z
  have eZ' := hsum Z'
  set X₁ := hpart1 (Hpk k r) Z
  set X₂ := hpart2 (Hpk k r) Z
  set Y₁ := hpart1 (Hpk k r) Z'
  set Y₂ := hpart2 (Hpk k r) Z'
  have dadd : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X + Y) = dOp π X + dOp π Y :=
    fun X Y hX hY => (hLin W k r z π hπ X Y hX hY).1
  have dsm : ∀ X (s : ℝ), InLieW k r z X → dOp π ((s : ℂ) • X) = (s : ℂ) • dOp π X := fun X s hX => by
    rw [(hLin W k r z π hπ X X hX hX).2 s, Complex.coe_smul]
  have dsub : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X - Y) = dOp π X - dOp π Y := fun X Y hX hY => by
    have e : X - Y = X + (((-1 : ℝ) : ℂ)) • Y := by simp [sub_eq_add_neg]
    rw [e, dadd _ _ hX (lie_smul hY _), dsm _ _ hY]
    simp [sub_eq_add_neg]
  have ecZ : ecOp π Z = dOp π X₁ + Complex.I • dOp π X₂ := rfl
  have ecZ' : ecOp π Z' = dOp π Y₁ + Complex.I • dOp π Y₂ := rfl
  refine ⟨?_, fun c => ?_, ?_⟩
  · have e : Z + Z' = (X₁ + Y₁) + Complex.I • (X₂ + Y₂) := by
      rw [← eZ, ← eZ', smul_add]; abel
    rw [e]
    refine ⟨gl_comb (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), ?_⟩
    rw [ec_comb π (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), dadd _ _ hX₁ hY₁, dadd _ _ hX₂ hY₂, ecZ, ecZ', smul_add]
    abel
  · have e : c • Z = ((c.re : ℂ) • X₁ - (c.im : ℂ) • X₂) + Complex.I • ((c.re : ℂ) • X₂ + (c.im : ℂ) • X₁) := by
      rw [alg_smul, Complex.re_add_im, eZ]
    have l1 := lie_sub (lie_smul hX₁ c.re) (lie_smul hX₂ c.im)
    have l2 := lie_add (lie_smul hX₂ c.re) (lie_smul hX₁ c.im)
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ (lie_smul hX₁ c.re) (lie_smul hX₂ c.im),
      dadd _ _ (lie_smul hX₂ c.re) (lie_smul hX₁ c.im), dsm X₁ c.re hX₁, dsm X₂ c.im hX₂, dsm X₂ c.re hX₂, dsm X₁ c.im hX₁, alg_smul, Complex.re_add_im, ecZ]
  · have b11 := hBr W k r z π hπ X₁ Y₁ hX₁ hY₁
    have b22 := hBr W k r z π hπ X₂ Y₂ hX₂ hY₂
    have b12 := hBr W k r z π hπ X₁ Y₂ hX₁ hY₂
    have b21 := hBr W k r z π hπ X₂ Y₁ hX₂ hY₁
    have e : Z * Z' - Z' * Z = ((X₁ * Y₁ - Y₁ * X₁) - (X₂ * Y₂ - Y₂ * X₂)) +
        Complex.I • ((X₁ * Y₂ - Y₂ * X₁) + (X₂ * Y₁ - Y₁ * X₂)) := by
      rw [← alg_bracket, eZ, eZ']
    have l1 := lie_sub b11.1 b22.1
    have l2 := lie_add b12.1 b21.1
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ b11.1 b22.1, dadd _ _ b12.1 b21.1, b11.2, b22.2, b12.2, b21.2, ecZ, ecZ']
    exact (alg_bracket (dOp π X₁) (dOp π X₂) (dOp π Y₁) (dOp π Y₂)).symm

namespace LieListProducts

theorem unitB_mul {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ)
    (ho : ∀ a b, herm H (Bs a) (Bs b) = if a = b then 1 else 0) (a b c d : Fin m) :
    unitB H Bs a b * unitB H Bs c d = if b = c then unitB H Bs a d else 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Qx8.unitB_mulVec H Bs c d, Matrix.mulVec_smul, Qx8.unitB_mulVec, ho]
  by_cases h : b = c
  · rw [if_pos h, if_pos h.symm, one_smul, Qx8.unitB_mulVec]
  · rw [if_neg h, if_neg (Ne.symm h), zero_smul, smul_zero, Matrix.zero_mulVec]

theorem list_prod_apply {W : Type*} [AddCommGroup W] [Module ℂ W] (L : List (Module.End ℂ W)) (v : W) :
    (L.map fun T : Module.End ℂ W => fun y : W => T y).foldr (fun T h => T h) v = L.prod v := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [ih]
    rfl

end LieListProducts

open LieListProducts in
theorem qr_frameGl_of : Qr.EcLie → Qr.FrameGl := by
  intro hE W _ _ _ k r m z π Bs hπ hB
  have hgl : ∀ a b, InGlW k r z (unitB (Hpk k r) Bs a b) := fun a b => frame_lie hB a b
  have h0 : InGlW k r z 0 ∧ ecOp π (0 : Mx k r) = 0 := by
    have h := (hE W k r z π hπ 0 0 ?_ ?_).2.1 0
    · simpa using h
    all_goals
      unfold InGlW
      rw [hpart1_lie (z := z) lie_zero, hpart2_lie (z := z) lie_zero]
      exact ⟨lie_zero, lie_zero⟩
  have hsub : ∀ Z Z', InGlW k r z Z → InGlW k r z Z' → ecOp π (Z - Z') = ecOp π Z - ecOp π Z' := by
    intro Z Z' hZ hZ'
    have h1 := (hE W k r z π hπ Z' Z' hZ' hZ').2.1 (-1)
    have h2 := (hE W k r z π hπ Z ((-1 : ℂ) • Z') hZ h1.1).1.2
    rw [h1.2] at h2
    simpa [sub_eq_add_neg] using h2
  have hite : ∀ (p : Prop) [Decidable p] (Z : Mx k r), InGlW k r z Z →
      InGlW k r z (if p then Z else 0) ∧ ecOp π (if p then Z else 0) = if p then ecOp π Z else 0 := by
    intro p _ Z hZ
    by_cases h : p
    · simpa [h] using hZ
    · simpa [h] using h0
  refine ⟨fun a b c d => ?_, fun w v => ?_⟩
  · have h := (hE W k r z π hπ _ _ (hgl a b) (hgl c d)).2.2.2
    rw [unitB_mul _ _ hB.2.1, unitB_mul _ _ hB.2.1, hsub _ _ (hite _ _ (hgl a d)).1 (hite _ _ (hgl c b)).1,
      (hite _ _ (hgl a d)).2, (hite _ _ (hgl c b)).2] at h
    unfold EB
    ext x
    have hx := congrArg (fun T : W →L[ℂ] W => T x) h
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] at hx ⊢ <;> exact hx.symm
  · unfold capRep qmF qdet qminor
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Module.End.mul_apply, ← list_prod_apply, List.map_ofFn]
    have e : ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • (1 : Module.End ℂ W) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [e, LinearMap.smul_apply, Module.End.one_apply]
    congr 3
    funext j y
    simp only [Function.comp, Tm, id, LinearMap.add_apply]
    rw [ecRep_eq hπ.1 hπ.2 (hgl _ _).1 (hgl _ _).2]
    congr 1
    by_cases h : σ j = j
    · simp [h, Algebra.algebraMap_eq_smul_one]
    · simp [h]

end Formalism.FourierDecayAlt.P
