import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyBoundaryDivisor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_boundary_divisor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → ∀ z : C.X,
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ξ : Sp A ⟶ C.X) (t : SAB H (Sp A))
      (_ : SABMap t C.t ξ) (P : PELUnif (maximalIdeal A) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X)
      (τ : Fin m → A) (k : ℕ),
      IsCN A ∧ ξ (closedPoint A) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue A).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
      Module.Free ℤ P.D.toPre.X ∧ Module.finrank ℤ P.D.toPre.X ≤ (Module.finrank ℚ E / 2 * (D.p + D.q)) ∧ IsCone id φ γ ∧
      ∀ y, ∃ (r : A) (u : Aˣ), PsiCoord P.D.toPre y r ∧ r ^ 2 = u * ∏ i, τ i ^ (k * (γ i y y).toNat) := by
  first | exact @GlobalTheory.SiegChart.exists_local_cone | exact GlobalTheory.SiegChart.exists_local_cone | (intros; apply GlobalTheory.SiegChart.exists_local_cone <;> assumption)
