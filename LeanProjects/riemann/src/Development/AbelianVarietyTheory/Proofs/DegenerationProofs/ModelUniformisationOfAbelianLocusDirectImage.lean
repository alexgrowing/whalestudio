import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonvanishingOfInvertiblePushforwardStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocusStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory

theorem isAdmissibleCompleteLocalDomainPrime_maximalIdeal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (h₁ : IsNoetherianRing R) (h₂ : IsIntegrallyClosed R) (h₃ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    admitted R (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨h₁, inferInstance, h₂, h₃⟩, h₃, inferInstance, (IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

theorem model_uniformisation_of_clauses : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  intro hL hL2 hL3 hL4 hL5 hE hU hP E _ _ _ H D l Xo c W₀ Y p hN R _ _ _ _ hR₁ hR₂ hR₃ ξ t ht hne hsp
  obtain ⟨-, hpol, hloc⟩ := T.generic_point_mem_moduli_of_meets_abelian_locus hL hL2 E H D l Xo c W₀ Y p hN R ξ t ht hne
  have hθ : ThetaNZ t.G t.PP.L := T.fibrewise_nonvanishing_of_invertible_pushforward E H Y.X Y.t hN.2.2.1 R ξ t ht
  have hadm : admitted R (IsLocalRing.maximalIdeal R) := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hR₁ hR₂ hR₃
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hpid : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
  have hsplit : SplitOver t.G (IsLocalRing.maximalIdeal R) := hsp
  obtain ⟨P, hP'⟩ := T.exists_uniformisation_complete_local_normal_prime hL hL2 hL3 hL4 hL5 hE hU hP E H R _ hadm hpid t hpol hsplit hθ
  have hopen : IsOpen (abLocus t.G) := by
    obtain ⟨U, hU', -⟩ := hN.2.2.2.1
    rw [← hloc, ← hU']
    exact U.isOpen.preimage ξ.continuous
  refine ⟨P, ?_, hP'⟩
  rw [hloc]
  exact T.pelTrivialisation_isUnit_on_abelianLocus hL hL2 hL3 hL4 hL5 E H R _ hadm t P hP' hopen

end GlobalTheory
