import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionLogNormPrime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_log_norm_prime : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → ∀ (M : HermLB q) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp q σ (M.div hr), logNorm (M.φ σ) r y = 0) → ∀ p : ℕ, p.Prime → (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField) ∧ (IsUnit (p : X.presheaf.stalk x) → UnitAt x (r i : X.functionField))) → ∀ (B : HermLB q) (ρ : B.B.ι → X.functionFieldˣ), IsRatSec B.B ρ → ∀ (ι : Type) (U : ι → X.Opens) (t : ι → X.functionFieldˣ), (∀ i, ∀ x ∈ M.B.U i, ¬ UnitAt x (r i : X.functionField) → (∃ a, x ∈ U a) ∧ (∀ a j, x ∈ U a → x ∈ B.B.U j → UnitAt x ((t a : X.functionField) * ρ j)) ∧ ∀ a b, x ∈ U a → x ∈ U b → RegAt x (((t a / t b : X.functionFieldˣ) - 1 : X.functionField) / r i)) → ∀ N : Fin n → HermLB q, num (Fin.cons (cl M) (Fin.cons (cl B) fun j => cl (N j))) = 0 := by
  first | exact @GlobalTheory.VertTriv.num_vert_triv | exact GlobalTheory.VertTriv.num_vert_triv | (intros; apply GlobalTheory.VertTriv.num_vert_triv <;> assumption)
