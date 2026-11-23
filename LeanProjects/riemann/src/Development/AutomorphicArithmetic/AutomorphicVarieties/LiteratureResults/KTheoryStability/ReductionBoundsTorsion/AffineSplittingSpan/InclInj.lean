import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

def EvCob : Prop :=
  ∀ (G : Type) [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ), Inv (MonoidHom.id G) e →
    ∀ z : Chn G (j + 1), IsCyc z → ev (MonoidHom.id G) (dC e) 1 z = 0

namespace GluingInclusion

set_option linter.unusedSectionVars false

variable (L : Type) [Field L] [NumberField L] (n r : ℕ)

abbrev Mt : Type := Matrix (Fin n) (Fin r) (𝓞 L)

def actE (M : Gm L n) : Multiplicative (Mt L n r) ≃* Multiplicative (Mt L n r) where
  toFun B := Multiplicative.ofAdd ((M : Matrix (Fin n) (Fin n) (𝓞 L)) * Multiplicative.toAdd B)
  invFun B := Multiplicative.ofAdd (((M⁻¹ : Gm L n) : Matrix (Fin n) (Fin n) (𝓞 L)) * Multiplicative.toAdd B)
  left_inv B := by simp [← Matrix.mul_assoc]
  right_inv B := by simp [← Matrix.mul_assoc]
  map_mul' B B' := by simp [Matrix.mul_add]

def act : Gm L n →* MulAut (Multiplicative (Mt L n r)) where
  toFun := actE L n r
  map_one' := MulEquiv.ext fun B => by simp [actE]
  map_mul' M M' := MulEquiv.ext fun B => by simp [actE, Matrix.mul_assoc]

abbrev Pb : Type := SemidirectProduct (Multiplicative (Mt L n r)) (Gm L n) (act L n r)

def blk (M : Matrix (Fin n) (Fin n) (𝓞 L)) (B : Mt L n r) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M B 0 1)

theorem blk_mul (M M' : Matrix (Fin n) (Fin n) (𝓞 L)) (B B' : Mt L n r) :
    blk L n r M B * blk L n r M' B' = blk L n r (M * M') (B + M * B') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem blk_one : blk L n r 1 0 = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one]
  simp

def incl : Pb L n r →* Gm L (n + r) where
  toFun x :=
    ⟨blk L n r (x.right : Matrix (Fin n) (Fin n) (𝓞 L)) (Multiplicative.toAdd x.left),
      blk L n r ((x.right⁻¹ : Gm L n) : Matrix (Fin n) (Fin n) (𝓞 L))
        (-(((x.right⁻¹ : Gm L n) : Matrix (Fin n) (Fin n) (𝓞 L)) * Multiplicative.toAdd x.left)),
      by rw [blk_mul, Units.mul_inv, Matrix.mul_neg, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
            add_neg_cancel, blk_one],
      by rw [blk_mul, Units.inv_mul, neg_add_cancel, blk_one]⟩
  map_one' := by
    ext : 1
    exact blk_one L n r
  map_mul' x y := by
    ext : 1
    change blk L n r _ _ = blk L n r _ _ * blk L n r _ _
    rw [blk_mul]
    rfl

end GluingInclusion

end PositivityTheory.KB.SplitAffineSpectral

end
