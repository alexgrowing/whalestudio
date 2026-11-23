import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh

namespace GlobalTheory.WignerGL

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def dualS (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  -(Ξ.dmat (toL (Matrix.single i j x)))ᵀ

def dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  (1 / 2 : ℂ) • (dualS Ξ i j (atEmb τ 1) - Complex.I • dualS Ξ i j (atEmb τ Complex.I))

def HasDualInfChar (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u : ℂ, Formalism.REAL.qdet (dualE Ξ τ) (u + ((a : ℂ) - 1) / 2) =
    (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

end GlobalTheory.WignerGL

namespace GlobalTheory.Published

def WignerVanishingGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a)
    (m m' : (E →+* ℂ) → Multiset ℂ), (∀ τ, π.HasInfChar τ (m τ)) → (∀ τ, WignerGL.HasDualInfChar Ξ τ (m' τ)) →
    m ≠ m' → ¬ IsCohFor π Ξ

end GlobalTheory.Published

end
