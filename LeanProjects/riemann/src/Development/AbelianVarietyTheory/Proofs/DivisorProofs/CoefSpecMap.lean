import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

def Rule.AgreeAt {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}
    (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) : Prop :=
  ∀ δ : X.DetGen, r.val R X trivial δ = s.val R X trivial δ

noncomputable def coefSpecMap {M : Scheme.{0}} {W : M.Opens} (hW : IsAffineOpen W) (R₀ : Type) [CommRing R₀] :
    Sp (R₀ ⊗[ℤ] Γ(M, W)) ⟶ M :=
  spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom ≫ hW.fromSpec

end GlobalTheory.RealMult
