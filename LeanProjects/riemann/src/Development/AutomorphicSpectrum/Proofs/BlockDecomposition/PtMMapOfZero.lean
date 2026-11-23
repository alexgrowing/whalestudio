import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellDecomp

section Gen

variable {R m : Type} [CommRing R] [Fintype m] [DecidableEq m]

theorem idem_compl {e : R} (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  have : (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
  rw [this, he]; ring

theorem idem_mul_compl {e : R} (he : e * e = e) : e * (1 - e) = 0 := by rw [mul_sub, he]; ring

def ptM (e : R) (he : e * e = e) : Matrix m m R →* Matrix m m R where
  toFun M := (1 - e) • 1 + e • M
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 := idem_compl he
    have h2 := idem_mul_compl he
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, h1, h2, h3, he,
      zero_smul, add_zero, zero_add]

theorem ptM_apply (e : R) (he : e * e = e) (M : Matrix m m R) : ptM e he M = (1 - e) • 1 + e • M := rfl

theorem cT_ptM (σ : R →+* R) {e : R} (he : e * e = e) (hσ : σ e = e) (M : Matrix m m R) :
    Formalism.UG.cT σ (ptM e he M) = ptM e he (Formalism.UG.cT σ M) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, ptM_apply, hσ]
  · simp [Formalism.UG.cT, ptM_apply, hσ, Matrix.one_apply, h, Ne.symm h]

theorem ptM_unitary (σ : R →+* R) {e : R} (he : e * e = e) (hσ : σ e = e) {J M : Matrix m m R}
    (hM : Formalism.UG.cT σ M * J * M = J) : Formalism.UG.cT σ (ptM e he M) * J * ptM e he M = J := by
  have h1 := idem_compl he
  have h2 := idem_mul_compl he
  have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
  rw [cT_ptM σ he hσ, ptM_apply, ptM_apply]
  simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, h1, h2, h3, he,
      zero_smul, add_zero, zero_add, hM]
  rw [← add_smul]; simp

theorem ptM_mul_compl {e : R} (he : e * e = e) (he' : (1 - e) * (1 - e) = 1 - e) (M N : Matrix m m R) :
    ptM e he M * ptM (1 - e) he' N = e • M + (1 - e) • N ∧ ptM (1 - e) he' N * ptM e he M = e • M + (1 - e) • N := by
  have h2 := idem_mul_compl he
  have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
  have h4 : (1 : R) - (1 - e) = e := by ring
  rw [ptM_apply, ptM_apply, h4]
  constructor
  · simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, he', h2, h3, he,
      zero_smul, add_zero, zero_add]
  · simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, he', h2, h3, he,
      zero_smul, add_zero, zero_add]
    exact add_comm _ _

end Gen

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

theorem blk_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  rw [blk4, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, blk4]

theorem blk_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  rw [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blk_add (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d + blk4 a' b' c' d' = blk4 (a + a') (b + b') (c + c') (d + d') := by
  rw [blk4, blk4, blk4, ← Matrix.fromBlocks_add]; rfl

theorem blk_smul (r : R) (a b c d : Matrix (Fin n) (Fin n) R) :
    r • blk4 a b c d = blk4 (r • a) (r • b) (r • c) (r • d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_smul]; rfl

theorem ptM_unip {e : R} (he : e * e = e) {y : Matrix (Fin n) (Fin n) R} (hy : e • y = y) :
    ptM e he (blk4 1 y 0 1) = blk4 1 y 0 1 := by
  have h1 : (1 - e) • (1 : Matrix (Fin n) (Fin n) R) + e • 1 = 1 := by rw [← add_smul]; simp
  rw [ptM_apply]
  nth_rw 1 [← blk_one]
  rw [blk_smul, blk_smul, blk_add]
  simp [h1, hy]

theorem blk_apply (a b c d : Matrix (Fin n) (Fin n) R) (x y : Fin n ⊕ Fin n) :
    blk4 a b c d (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks a b c d x y := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem weyl_mulVec (y : Fin (n + n) → R) (i : Fin n) :
    ((blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).mulVec y) (finSumFinEquiv (Sum.inl i)) =
      y (finSumFinEquiv (Sum.inr i)) ∧
    ((blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).mulVec y) (finSumFinEquiv (Sum.inr i)) =
      -y (finSumFinEquiv (Sum.inl i)) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp]
  simp only [blk_apply, Fintype.sum_sum_type]
  simp [Matrix.one_apply]

end Blocks

end GlobalTheory.CompanionTheory.CellDecomp

namespace GlobalTheory.CompanionTheory.CellDecomp

section Gen2

variable {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ}

theorem weyl_map (φ : R →+* R') :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map φ = blk4 (0 : Matrix (Fin n) (Fin n) R') 1 (-1) 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.map_apply, blk_apply, blk_apply]
  rcases i with i | i <;> rcases j with j | j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_compl_zero (φ : R →+* R') {e : R} (h : φ e = 1) : φ (1 - e) = 0 := by
  rw [map_sub, map_one, h, sub_self]

theorem map_compl_one (φ : R →+* R') {e : R} (h : φ e = 0) : φ (1 - e) = 1 := by
  rw [map_sub, map_one, h, sub_zero]

theorem bc_val {m : Type} [Fintype m] [DecidableEq m] (φ : R →+* R') (g : GL m R) :
    (Formalism.UG.bc φ g).1 = g.1.map φ := rfl

theorem cell_alg {e : R} {c d y : Matrix (Fin n) (Fin n) R} (h : (e • c) * y = e • d) :
    e • (c * -y + d * 1) = 0 := by
  rw [smul_add, mul_neg, smul_neg, mul_one, ← smul_mul_assoc, h, neg_add_cancel]

theorem weyl_inv (y : Matrix (Fin n) (Fin n) R) :
    blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0 * blk4 1 y 0 1 * blk4 (-y) (-1) 1 0 = 1 := by
  rw [blk_mul, blk_mul, ← blk_one]
  simp

end Gen2

section Abs

variable {Γ : Type} [Group Γ]

theorem assemble (A B : Γ →* Γ) (comm : ∀ x y, A x * B y = B y * A x) (hAB : ∀ x, A x * B x = x)
    {g q₀ k₀ w n : Γ} (hn : A n = n) (hg : g = q₀ * k₀) :
    g = A (g * (w * n)⁻¹) * B q₀ * (w * n) * B (w⁻¹ * k₀) := by
  have hh : w * n = A (w * n) * B w := by
    rw [map_mul, hn]
    calc w * n = A w * B w * n := by rw [hAB]
      _ = A w * (B w * A n) := by rw [mul_assoc, hn]
      _ = A w * n * B w := by rw [← comm, hn, mul_assoc]
  calc g = A g * B g := (hAB g).symm
    _ = A (g * (w * n)⁻¹) * A (w * n) * (B q₀ * B k₀) := by
        rw [← map_mul A, inv_mul_cancel_right, ← map_mul B, ← hg]
    _ = A (g * (w * n)⁻¹) * (B q₀ * A (w * n)) * B k₀ := by rw [← comm]; group
    _ = A (g * (w * n)⁻¹) * B q₀ * (A (w * n) * B w) * ((B w)⁻¹ * B k₀) := by group
    _ = A (g * (w * n)⁻¹) * B q₀ * (w * n) * B (w⁻¹ * k₀) := by rw [← hh, map_mul B, map_inv]

end Abs

end GlobalTheory.CompanionTheory.CellDecomp

namespace GlobalTheory.CompanionTheory.CellDecomp

section Map

variable {R R' m : Type} [CommRing R] [CommRing R'] [Fintype m] [DecidableEq m]

theorem ptM_map_of_zero (φ : R →+* R') {f : R} (hf : f * f = f) (h : φ f = 0) (M : Matrix m m R) :
    (ptM f hf M).map φ = 1 := by
  ext i j
  by_cases e : i = j
  · subst e; simp [ptM_apply, h]
  · simp [ptM_apply, h, Matrix.one_apply, e]

theorem ptM_map_of_one (φ : R →+* R') {f : R} (hf : f * f = f) (h : φ f = 1) (M : Matrix m m R) :
    (ptM f hf M).map φ = M.map φ := by
  ext i j
  by_cases e : i = j
  · subst e; simp [ptM_apply, h]
  · simp [ptM_apply, h, Matrix.one_apply, e]

end Map

section Grp

variable {D : D7} {n : ℕ}

theorem mat_inj {x y : G D n} (h : mat x = mat y) : x = y :=
  matHom_injective _ _ _ (Units.ext h)

theorem mat_mul' (x y : G D n) : mat (x * y) = mat x * mat y := rfl

theorem mat_one' : mat (1 : G D n) = 1 := rfl

def pt (e : AE D) (he : e * e = e) (hc : cA D e = e) : G D n →* G D n :=
  ((Units.map (ptM e he : Mx D (n + n) (n + n) →* Mx D (n + n) (n + n))).comp
    (matHom _ D.sp.cm.sig (Jst D n))).codRestrict (HR _ D.sp.cm.sig (Jst D n))
    (fun x => ptM_unitary (cA D) he hc x.2)

theorem mat_pt (e : AE D) (he : e * e = e) (hc : cA D e = e) (x : G D n) : mat (pt e he hc x) = ptM e he (mat x) := rfl

def bB (g : G D n) : Mx D n n := ((mat g).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

theorem cB_mul (x y : G D n) : cB (x * y) = cB x * blkA (mat y) + dB x * cB y := by
  ext i j
  simp only [cB, dB, blkA, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.mul_apply, mat_mul']
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]

theorem dB_mul (x y : G D n) : dB (x * y) = cB x * bB y + dB x * dB y := by
  ext i j
  simp only [cB, dB, bB, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.mul_apply, mat_mul']
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]

theorem cB_of {x : G D n} {a b c d : Mx D n n} (h : mat x = blk4 a b c d) : cB x = c := by
  ext i j
  simp only [cB, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, h, blk_apply, Matrix.fromBlocks_apply₂₁]

theorem dB_of {x : G D n} {a b c d : Mx D n n} (h : mat x = blk4 a b c d) : dB x = d := by
  ext i j
  simp only [dB, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, h, blk_apply, Matrix.fromBlocks_apply₂₂]

theorem blkA_of {x : G D n} {a b c d : Mx D n n} (h : mat x = blk4 a b c d) : blkA (mat x) = a := by
  ext i j
  simp only [blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, h, blk_apply, Matrix.fromBlocks_apply₁₁]

theorem cB_pt (e : AE D) (he : e * e = e) (hc : cA D e = e) (x : G D n) : cB (pt e he hc x) = e • cB x := by
  ext i j
  have hne : (finSumFinEquiv (Sum.inr i) : Fin (n + n)) ≠ finSumFinEquiv (Sum.inl j) := by
    rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
  simp only [cB, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, mat_pt, ptM_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero, zero_add]

theorem cB_inv {q : G D n} (h : cB q = 0) : cB q⁻¹ = 0 := by
  have h1 : mat (1 : G D n) = blk4 1 0 0 1 := by rw [mat_one', blk_one]
  have c1 := cB_mul q q⁻¹
  have d1 := dB_mul q q⁻¹
  rw [mul_inv_cancel, cB_of h1, h, zero_mul, zero_add] at c1
  rw [mul_inv_cancel, dB_of h1, h, zero_mul, zero_add] at d1
  have d2 : dB q⁻¹ * dB q = 1 := mul_eq_one_comm.1 d1.symm
  calc cB q⁻¹ = (dB q⁻¹ * dB q) * cB q⁻¹ := by rw [d2, one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, ← c1, mul_zero]

theorem mem_siegelParabolic_of_lowerLeft_eq_zero {g : G D n} (h : cB g = 0) : g ∈ P D n := by
  have key : ∀ g : G D n, cB g = 0 → ∀ x ∈ upperHalf D n, (mat g).mulVec x ∈ upperHalf D n := by
    intro g h x hx
    have h' : ∀ i j, mat g (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := fun i j => congrFun (congrFun h i) j
    ext i
    have hx' : ∀ j, x (finSumFinEquiv (Sum.inr j : Fin n ⊕ Fin n)) = 0 := fun j => congrFun hx j
    simp only [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [h', hx', zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  refine fun x => ⟨key g h x, fun hx => ?_⟩
  have := key _ (cB_inv h) _ hx
  change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
  rwa [Matrix.mulVec_mulVec, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mulVec] at this

theorem cB_of_mem_P {q : G D n} (h : q ∈ P D n) : cB q = 0 := by
  ext i j
  exact GlobalTheory.StdUnn.HeightExists.lower_eq_zero h i j

end Grp

end GlobalTheory.CompanionTheory.CellDecomp

end
