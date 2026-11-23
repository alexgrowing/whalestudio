import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_base_change_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω') ⟶ Z) (h : Z ⟶ A.X), (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (seg y') → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → Smooth h → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li), A'.ξ ≫ e.hom = ξ' ∧ HodgeOver A' A (e.hom ≫ h) i j ∧ A'.R = A.R ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | exact GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth <;> assumption)
