import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace PositivityTheory.Affgl.CT

def splitEquiv {a r : ℕ} (h : r ≤ a) : Fin r ⊕ Fin (a - r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le h))

def blockMat {R : Type} [CommRing R] {a r : ℕ} (h : r ≤ a) (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin (a - r)) (Fin (a - r)) R) : Matrix (Fin a) (Fin a) R :=
  Matrix.reindex (splitEquiv h) (splitEquiv h) (Matrix.fromBlocks A 0 0 B)

theorem blockMat_mul {R : Type} [CommRing R] {a r : ℕ} (h : r ≤ a) (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin (a - r)) (Fin (a - r)) R) :
    blockMat h A B * blockMat h A' B' = blockMat h (A * A') (B * B') := by
  simp [blockMat, Matrix.fromBlocks_multiply]

theorem blockMat_one {R : Type} [CommRing R] {a r : ℕ} (h : r ≤ a) :
    blockMat h (1 : Matrix (Fin r) (Fin r) R) 1 = 1 := by
  simp [blockMat, Matrix.fromBlocks_one]

def blockGL {R : Type} [CommRing R] {a r : ℕ} (h : r ≤ a) :
    GL (Fin r) R × GL (Fin (a - r)) R →* GL (Fin a) R where
  toFun p := ⟨blockMat h p.1 p.2, blockMat h ↑(p.1⁻¹) ↑(p.2⁻¹),
    by rw [blockMat_mul, Units.mul_inv, Units.mul_inv, blockMat_one],
    by rw [blockMat_mul, Units.inv_mul, Units.inv_mul, blockMat_one]⟩
  map_one' := Units.ext (blockMat_one h)
  map_mul' p q := Units.ext (blockMat_mul h _ _ _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

def ct [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (φ : GA E a → ℂ) : GA E a → ℂ :=
  fun g => ∫ x in 𝓕, φ (unip x * g) ∂μ

end PositivityTheory.Affgl.CT

end
