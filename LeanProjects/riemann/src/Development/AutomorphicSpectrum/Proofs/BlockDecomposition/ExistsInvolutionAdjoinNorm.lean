import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
  GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.SgRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (x : E) : conjE E (conjE E x) = x :=
  IsCMField.complexConj_apply_apply E x

def bar (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E := (X.map (conjE E))ᵀ

theorem bar_mul (X Y : Matrix (Fin n) (Fin n) E) : bar (X * Y) = bar Y * bar X := by
  rw [bar, bar, bar, Matrix.map_mul, Matrix.transpose_mul]

theorem bar_add (X Y : Matrix (Fin n) (Fin n) E) : bar (X + Y) = bar X + bar Y := by
  ext i j; simp [bar]

theorem bar_bar (X : Matrix (Fin n) (Fin n) E) : bar (bar X) = X := by
  ext i j; simp [bar, conj_conj]

theorem bar_algebraMap (r : E) :
    bar (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [bar, Matrix.algebraMap_matrix_apply]
  · simp [bar, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

theorem sg_eq (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : sg d X = d.val * bar X * (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_val (d : GL (Fin n) E) : (nrm d).val = d.val * bar (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_inv_val (d : GL (Fin n) E) :
    ((nrm d)⁻¹ : GL (Fin n) E).val = bar d.val * (d⁻¹ : GL (Fin n) E).val := rfl

theorem sg_add (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X + Y) = sg d X + sg d Y := by
  rw [sg_eq, sg_eq, sg_eq, bar_add, Matrix.mul_add, Matrix.add_mul]

theorem sg_mul (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X * Y) = sg d Y * sg d X := by
  have h : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  calc sg d (X * Y) = d.val * bar Y * 1 * bar X * (d⁻¹ : GL (Fin n) E).val := by
        rw [sg_eq, bar_mul]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = sg d Y * sg d X := by
        rw [← h, sg_eq, sg_eq]; simp only [Matrix.mul_assoc]

theorem sg_algebraMap (d : GL (Fin n) E) (r : E) :
    sg d (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [sg_eq, bar_algebraMap, ← Algebra.commutes, Matrix.mul_assoc, h, Matrix.mul_one]

theorem sg_one (d : GL (Fin n) E) : sg d 1 = 1 := by
  have h := sg_algebraMap d 1
  simpa using h

theorem sg_zero (d : GL (Fin n) E) : sg d 0 = 0 := by
  have h := sg_algebraMap d 0
  simpa using h

theorem sg_nrm (d : GL (Fin n) E) : sg d (nrm d).val = ((nrm d)⁻¹ : GL (Fin n) E).val := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [nrm_inv_val, sg_eq, nrm_val, bar_mul, bar_bar, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem sg_sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) :
    sg d (sg d X) = (nrm d).val * X * ((nrm d)⁻¹ : GL (Fin n) E).val := by
  rw [nrm_inv_val, nrm_val, sg_eq, sg_eq, bar_mul, bar_mul, bar_bar]
  simp only [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in

theorem inv_mem (g : GL (Fin n) E) : (g⁻¹ : GL (Fin n) E).val ∈ Algebra.adjoin E {g.val} := by
  have hdet : g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hc : g.val.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  have hp : aeval g.val g.val.charpoly = 0 := Matrix.aeval_self_charpoly _
  set q : Matrix (Fin n) (Fin n) E := aeval g.val (divX g.val.charpoly) with hq
  have hd : q * g.val + algebraMap E _ (g.val.charpoly.coeff 0) = 0 := by
    have h := congrArg (aeval g.val) (divX_mul_X_add g.val.charpoly)
    rwa [hp, map_add, map_mul, aeval_X, aeval_C] at h
  have hmem : q ∈ Algebra.adjoin E {g.val} := aeval_mem_adjoin_singleton E g.val
  have h1 : (-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val = 1 := by
    rw [Matrix.smul_mul, eq_neg_of_add_eq_zero_left hd, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, neg_neg,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : (g⁻¹ : GL (Fin n) E).val = -(g.val.charpoly.coeff 0)⁻¹ • q := by
    calc (g⁻¹ : GL (Fin n) E).val = ((-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val) * (g⁻¹ : GL (Fin n) E).val := by
          rw [h1, Matrix.one_mul]
      _ = -(g.val.charpoly.coeff 0)⁻¹ • q := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  exact Subalgebra.smul_mem _ hmem _

theorem sg_mem (d : GL (Fin n) E) {x : Matrix (Fin n) (Fin n) E} (hx : x ∈ Algebra.adjoin E {(nrm d).val}) :
    sg d x ∈ Algebra.adjoin E {(nrm d).val} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.1 hx
    rw [sg_nrm]
    exact inv_mem (nrm d)
  | algebraMap r =>
    rw [sg_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [sg_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [sg_mul]
    exact mul_mem hy hx

omit [NumberField E] [IsCMField E] in
theorem adjoin_comm (γ : Matrix (Fin n) (Fin n) E) {x y : Matrix (Fin n) (Fin n) E}
    (hx : x ∈ Algebra.adjoin E {γ}) (hy : y ∈ Algebra.adjoin E {γ}) : x * y = y * x :=
  pol_comm γ x y ((isPol_iff γ x).2 hx) ((isPol_iff γ y).2 hy)

theorem exists_sgRing (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) :
    ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val},
      (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  refine ⟨{ toFun := fun x => ⟨sg d x, sg_mem d x.2⟩
            map_one' := Subtype.ext (sg_one d)
            map_zero' := Subtype.ext (sg_zero d)
            map_add' := fun x y => Subtype.ext (sg_add d x y)
            map_mul' := fun x y => Subtype.ext ?_ }, fun x => rfl, fun x => Subtype.ext ?_⟩
  · change sg d (x.val * y.val) = sg d x.val * sg d y.val
    rw [sg_mul]
    exact adjoin_comm _ (sg_mem d y.2) (sg_mem d x.2)
  · change sg d (sg d x.val) = x.val
    have hγ : (nrm d).val ∈ Algebra.adjoin E {(nrm d).val} := Algebra.self_mem_adjoin_singleton E _
    rw [sg_sg, adjoin_comm _ hγ x.2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.CompanionTheory.TorusCh.SgRing

end
