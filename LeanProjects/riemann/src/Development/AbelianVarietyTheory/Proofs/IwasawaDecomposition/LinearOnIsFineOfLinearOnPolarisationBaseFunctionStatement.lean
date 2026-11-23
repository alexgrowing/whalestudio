import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearOn_isFine_of_linearOn_polarisationBaseFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], 0 < D → IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms H.bar X) → (∀ i y, 0 ≤ γ i y y) → (baseFun (𝓞 E) D φs 𝓜).LinearOn γ → (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  first | exact @GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | exact GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | (intros; apply GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun <;> assumption)
