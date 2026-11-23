import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCpt
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_root_hodge_cpt : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ) (ζ : Ωˣ), p ∈ S → 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → IsPrimitiveRoot ζ (p ^ 𝔐.R p) → ∃ (τ : (Fin (D.p + D.q) → 𝓞 E) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G)) (ew : (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) → Ωˣ) (e : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p)), (∀ x x', τ (x + x') = τ x * τ x') ∧ (∀ (a : 𝓞 E) x, τ (a • x) = τ x ≫ 𝔐.t.act.act a) ∧ (∀ g, g ^ (p ^ 𝔐.R p) = 1 ↔ ∃ x, τ x = g) ∧ GenWeil 𝔐.t.G 𝔐.t.PP.L 𝔐.ξ (p ^ 𝔐.R p) ew ∧ (∀ x x', ew (τ x) (τ x') = ζ ^ (e x x').val) ∧ (∀ x, e x x = 0) ∧ (∀ (a : 𝓞 E) x x', e (a • x) x' = e x (RingOfIntegers.mapRingEquiv (HT.cmConj E) a • x')) ∧ (∀ φ : (Fin (D.p + D.q) → 𝓞 E) →+ ZMod (p ^ 𝔐.R p), ∃ x, e x = φ) ∧ ∀ x, e x = 0 → ∃ x', x = (p ^ 𝔐.R p) • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HF.generic_torsion | exact GlobalTheory.CompanionTheory.Ar.HF.generic_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.HF.generic_torsion <;> assumption)
