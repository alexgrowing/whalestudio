import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
import Formalism.RealPlaceAnalysis.StatementB

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.WigAlg

def cx {E : Type} [Field E] {a : ℕ} {N : Type} [AddCommGroup N] [Module ℂ N] (τ : E →+* ℂ) (φ : Lie E a → N)
    (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (φ (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • φ (toL (Matrix.single i j (atEmb τ Complex.I))))

def tpr {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (A B : Fin n → Fin n → Module.End ℂ M) (p r : ℕ)
    (φ : Fin n → Fin n → M) : M :=
  ∑ x, ∑ y, ∑ z, epow A p x y (epow B r x z (φ y z))

end GlobalTheory.WigAlg

end
