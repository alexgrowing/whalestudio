import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_projective_model : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (R : ℕ → ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), Flat.NormalCpt M₁.ξ → M₁.ξ ≫ f₁ = y₀ ≫ Y.j → f₁ (GlobalTheory.CompanionTheory.Ar.genPt M₁.ξ) ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, 4 ≤ R p) → (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ M₁.X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ M₁.ξ g (RingHom.id Ω) ∧ 𝔐.f = g ≫ f₁ ∧ 𝔐.R = R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ ∀ q ∈ genFib M₁.ξ, IsoAt 𝔐.ξ g (RingHom.id Ω) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopHodge.exists_hodgeCpt_htFree | exact GlobalTheory.CompanionTheory.Ar.TopHodge.exists_hodgeCpt_htFree | (intros; apply GlobalTheory.CompanionTheory.Ar.TopHodge.exists_hodgeCpt_htFree <;> assumption)
