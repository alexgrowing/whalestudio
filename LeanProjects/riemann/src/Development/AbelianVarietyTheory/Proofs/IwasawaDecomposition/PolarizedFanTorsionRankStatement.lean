import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizedFanTorsionRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_fan_torsion_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g d : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ)
    (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → Refines H q φs 𝒩 φ → Module.Projective (𝓞 E) P.D.toPre.X →
    Module.finrank (𝓞 E) P.D.toPre.X ≤ q → IsCN R → ConeO H φ P.D.toPre.X m γ → InCone P.D.toPre γ →
    ∃ q : FractionRing R, q ≠ 0 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V,
      Irreducible ϖ → ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
      (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) → ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
      ∃ (n : ℤ) (w : Vˣ), (n : ℝ) = d * (resInt (𝓞 E) φs).evalZ be ∧ gam q = algebraMap V _ w * algebraMap V _ ϖ ^ n := by
  first | exact @GlobalTheory.TorRef.ChartMono.exists_monomial | exact GlobalTheory.TorRef.ChartMono.exists_monomial | (intros; apply GlobalTheory.TorRef.ChartMono.exists_monomial <;> assumption)
