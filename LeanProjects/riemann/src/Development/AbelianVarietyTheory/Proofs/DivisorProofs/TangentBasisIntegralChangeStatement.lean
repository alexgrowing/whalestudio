import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegralChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_integral_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X} (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G), TanBasis t b → ∃ (m : ℕ) (r : Fin m → 𝓞 K) (M : Fin m → Matrix (Fin n) (Fin n) K), Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧ (∀ c, c ∈ lieCoordLat t hx b ↔ ∀ i, ∃ (k : ℕ) (a : Fin n → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j) ∧ ∀ (i : Fin m) (S : Type) [CommRing S] (ψ : 𝓞 K →+* S), IsUnit (ψ (r i)) → ∀ (T : Type) [Field T] (ι' : S →+* T) (j : K →+* T), ι'.comp ψ = j.comp (algebraMap (𝓞 K) K) → ∀ (xT : Sp T ⟶ X) (hT : spMap j ≫ xK = xT) (vO : Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t (spMap ψ ≫ xO) vO → ∃ a : Fin n → S, spMap (dualMap ι') ≫ vO = combLeft t (fun q => bcTan j hT (b q)) (∑ s, ι' (a s) • fun q => j (M i s q)) := by
  first | exact @GlobalTheory.LieCover.exists_cover_lieCoordLat | exact GlobalTheory.LieCover.exists_cover_lieCoordLat | (intros; apply GlobalTheory.LieCover.exists_cover_lieCoordLat <;> assumption)
