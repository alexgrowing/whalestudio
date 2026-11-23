import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusExtendsNormalLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_extends_normal_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (K : Type) [Field K] [CharZero K]
    (ξ : Sp K ⟶ X) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → SplitK t ξ q →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] [Algebra R K] [IsFractionRing R K]
    (x : Sp R ⟶ X), spMap (algebraMap R K) ≫ x = ξ →
    ∀ (p : ℕ) [Fact p.Prime] (ψ : R →+* ↥(intO ℂ_[p])) (z : Sp ↥(intO ℂ_[p]) ⟶ X), IsLocalHom ψ → spMap ψ ≫ x = z →
    ∀ (N : ℕ) (χ : Fin N → (TorsK t ξ q →* Kˣ)) (ch : Fin N → TorsChar t z q) (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ),
    (∀ (α : 𝓞 E) (k k' : TorsK t ξ q), k'.1 = k.1 ≫ t.act.act α → ∀ m, χ m k' = ∏ m', χ m' k ^ ρ α m m') →
    (∀ m, InducedBy (χ m) x (algebraMap R K) ψ (ch m)) → GlobalTheory.EqHalf.Equivar t ch ρ := by
  first | exact @GlobalTheory.EqHalf.InducedProof.equivar_induced | exact GlobalTheory.EqHalf.InducedProof.equivar_induced | (intros; apply GlobalTheory.EqHalf.InducedProof.equivar_induced <;> assumption)
