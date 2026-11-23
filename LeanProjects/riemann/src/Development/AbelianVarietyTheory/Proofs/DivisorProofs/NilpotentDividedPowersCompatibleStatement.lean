import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentDividedPowersCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_divided_powers_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' B B' : Type} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] {K : Ideal B} {K' : Ideal B'}
    (κ : DividedPowers K) (κ' : DividedPowers K'), IsNilDP κ → IsNilDP κ' →
    ∀ (π : B →+* R) (π' : B' →+* R'), Function.Surjective π → Function.Surjective π' →
    RingHom.ker π = K → RingHom.ker π' = K' → ∀ (τ : B →+* B') (σ : R →+* R')
    {X₀ : Obj F 𝔠 (Sp R)} {Z : Obj F 𝔠 (Sp B)} {i : X₀.A.left ⟶ Z.A.left}, X₀.IsPullBy Z (spMap π) i →
    ∀ {X₁ : Obj F 𝔠 (Sp R')} {Z' : Obj F 𝔠 (Sp B')} {i' : X₁.A.left ⟶ Z'.A.left}, X₁.IsPullBy Z' (spMap π') i' →
    ∀ {q : Z'.A.left ⟶ Z.A.left}, Z'.IsPullBy Z (spMap τ) q → ∀ {p : X₁.A.left ⟶ X₀.A.left}, i' ≫ q = p ≫ i →
    ∀ (M : GrpMor κ (spMap π) X₀.A κ' (spMap π') X₁.A τ (spMap σ) p) (d : Crys κ (spMap π) X₀.A),
    ∃ d', M.Corr d d' := by
  first | exact @GlobalTheory.LatJet.crys_exists_corr | exact GlobalTheory.LatJet.crys_exists_corr | (intros; apply GlobalTheory.LatJet.crys_exists_corr <;> assumption)
