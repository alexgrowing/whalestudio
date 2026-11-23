import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InConeOfCoordinateSquaresStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisorStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory

namespace GlobalTheory.SiegLoc

theorem isCone_of_agreesPsd (g : ℕ) (φ φs : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    [Module.Free ℤ X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hX : Module.finrank ℤ X ≤ g)
    (hA : AgreesPsd g φs φ) (hc : IsCone id φ γ) : IsCone id φs γ :=
  TameZ.isCone_of_agree (fun B hB => (hA X hX B hB).symm) hc

theorem hasCones_of_siegPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ φs : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → AgreesPsd (Module.finrank ℚ E / 2 * (D.p + D.q)) φs φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → HasCones (ConeZ E φs) C := by
  intro E _ _ _ H D l Xo c n R _ b ω φ φs F S s j _ G _ e BD d N κ C π hpq hn hodd hM hfan hag hded hb hloc hS hκ hP z
  obtain ⟨A, _, _, _, ξ, t, m0, P, m, γ, τ, k, hCN, hz, hE, hU, hT, hfree, hrk, hc, hmono⟩ :=
    GlobalTheory.T.siegel_family_boundary_divisor E H D l Xo c n R b ω φ F S s j G e BD d N κ C π hpq hn hodd hM hfan hded hb hloc hS hκ hP z
  refine ⟨A, _, _, _, ξ, t, m0, P, m, γ, hCN, hz, hE, hU, hT, ?_, ?_⟩
  · exact isCone_of_agreesPsd _ φ φs _ m γ hrk hag hc
  · exact GlobalTheory.T.inCone_of_coordinate_squares A P.D.toPre m τ k γ (fun i y z => (hc.mem i).1 y z) hc.nonneg hmono

end GlobalTheory.SiegLoc
