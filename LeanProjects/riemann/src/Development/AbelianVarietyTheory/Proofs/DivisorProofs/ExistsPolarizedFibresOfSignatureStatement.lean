import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedFibresOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarized_fibres_of_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (_ : Level H) (R : Type) [CommRing R] (σ : R →+* ℂ) (Q : PAT H (Sp R)) (ρ : ℂ) (p q : ℕ), ρ ^ 2 = -(H.d : ℂ) → (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = ρ → LieMult Q.t.act (spMap σ) τ p) ∧ (τ H.rt ≠ ρ → LieMult Q.t.act (spMap σ) τ q)) → ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (P₁ : Out.PolAV (Sp ℂ)) (φ : P₁.A.left ⟶ Q.pol.A.left) (φ₀ : P₁.A.left ⟶ P₀.A.left), TrLe K (Module.finrank ℚ E / 2 * p * q) ∧ IsPolFibre σ Q.pol P₁ φ ∧ IsPolFibre ι P₀ P₁ φ₀ := by
  first | exact @GlobalTheory.BdDim.CxField.exists_field_of_signature | exact GlobalTheory.BdDim.CxField.exists_field_of_signature | (intros; apply GlobalTheory.BdDim.CxField.exists_field_of_signature <;> assumption)
