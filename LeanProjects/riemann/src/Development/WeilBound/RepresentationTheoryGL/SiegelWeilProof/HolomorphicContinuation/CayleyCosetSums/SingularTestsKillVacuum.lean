import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.EventuallyUnit

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

theorem lt3 : SingularTestsKillVacuum := by
  intro n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ ha hb hx
  have mulG : ∀ {p q : M2 n}, InG p → InG q → InG (p * q) := by
    intro p q hp hq
    unfold InG at *
    calc (p * q)ᴴ * JJ n * (p * q) = qᴴ * (pᴴ * JJ n * p) * q := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hp, hq]
  have hG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have h : ∀ k, ∫ t, fz m e 0 (x * ι k * a * nU (herm t) * b) * ψ t = 0 := fun k =>
    L3.vanish_all hmn e _ b (mulG (mulG hx (hG k)) ha) hb ψ hψ
  simp only [tOp, h, mul_zero, integral_zero]

end PositivityTheory.Rg.Sw.HSt
