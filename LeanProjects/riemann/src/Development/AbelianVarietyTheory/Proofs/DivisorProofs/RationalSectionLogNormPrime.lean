import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorMultiplicityPPositiveOrderStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

namespace GlobalTheory.VertTriv

theorem num_vert_triv : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → ∀ (M : HermLB q) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (∀ σ, ∀ y ∈ offSupp q σ (M.div hr), logNorm (M.φ σ) r y = 0) → ∀ p : ℕ, p.Prime → (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField) ∧ (IsUnit (p : X.presheaf.stalk x) → UnitAt x (r i : X.functionField))) → ∀ (B : HermLB q) (ρ : B.B.ι → X.functionFieldˣ), IsRatSec B.B ρ → ∀ (ι : Type) (U : ι → X.Opens) (t : ι → X.functionFieldˣ), (∀ i, ∀ x ∈ M.B.U i, ¬ UnitAt x (r i : X.functionField) → (∃ a, x ∈ U a) ∧ (∀ a j, x ∈ U a → x ∈ B.B.U j → UnitAt x ((t a : X.functionField) * ρ j)) ∧ ∀ a b, x ∈ U a → x ∈ U b → RegAt x (((t a / t b : X.functionFieldˣ) - 1 : X.functionField) / r i)) → ∀ N : Fin n → HermLB q, num (Fin.cons (cl M) (Fin.cons (cl B) fun j => cl (N j))) = 0 := by
  intro hP k _ X _ _ q n hX num hn M r hr hinf p hp hreg B ρ hρ ι U t hfr N
  haveI := Fact.mk hp
  have key := GlobalTheory.T.height_of_rational_section_via_divisor hP k X q (n + 1) hX num hn M r hr hinf (Fin.cons B N) (fun _ => p) (fun _ => 0)
    (fun z hz => ?_)
  · have e : (fun j => cl ((Fin.cons B N : Fin (n + 1) → HermLB q) j)) = Fin.cons (cl B) (fun j => cl (N j)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [e] at key
    rw [key]
    simp
  · obtain ⟨hpos, hZpts⟩ := GlobalTheory.T.divisor_multiplicity_p_positive_order k X q (n + 1) hX M r hr p hp hreg z hz
    obtain ⟨Z, i, hi, hZ, hA, e₁, e₂⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre k X q (n + 1) hX p z hpos
    refine ⟨inferInstance, Z, i, hi, hZ, hA, e₁, e₂, ?_⟩
    have h0 := GlobalTheory.T.rational_section_divisor_comparison X k q M r (fun j x hx => (hreg j x hx).1) B ρ hρ ι U t hfr Z i (hZpts Z i e₁)
    rw [interNum_eq_zero_of_cls_eq_zero (ZMod p) (structureModule Z)
      (fun j => LB.isLB_pull ((Fin.cons B N : Fin (n + 1) → HermLB q) j).isLB i) 0 (by simpa using h0), Int.cast_zero]

end GlobalTheory.VertTriv

end
