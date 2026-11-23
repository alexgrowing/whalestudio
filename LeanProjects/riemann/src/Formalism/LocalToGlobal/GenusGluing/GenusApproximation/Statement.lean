import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.ComplF

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

def WeakApproxU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : Prop :=
  ∀ x ∈ UAd hc n, ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ ∈ URat hc n,
    IntAt v (((Formalism.UG.bc (iA F E) γ)⁻¹ * x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∧
    IntAt v ((x⁻¹ * Formalism.UG.bc (iA F E) γ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))

def GenusToPoint : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N →
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) N → ∃ x ∈ UAd hc n, Formalism.UG.CS.globLat x (stdLat E n) = N

def PointToGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → ∀ x ∈ UAd hc n,
    Formalism.HermitianLatticesTheory.SameGenus (hStd E n) (stdLat E n) (Formalism.UG.CS.globLat x (stdLat E n))

def LocToAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), UnimodGenusLoc E n → UnimodGenus hc n

def AdToLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → UnimodGenus hc n → UnimodGenusLoc E n

def Bridge : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ), WeakApproxU hc n → (UnimodGenusLoc E n ↔ UnimodGenus hc n)

end Formalism.L2.GenusGluing.Gen
