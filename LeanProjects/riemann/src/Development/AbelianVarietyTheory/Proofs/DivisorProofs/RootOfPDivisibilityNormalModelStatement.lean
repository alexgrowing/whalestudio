import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfPDivisibilityNormalModel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_of_p_divisibility_normal_model : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} (hB : GlobalTheory.IsNormalScheme B.X) (g γ : Γ(B.X, ⊤)) (m : ℕ) (hg : IsRootOfP p g p) (hγ : IsRootOfP p γ (p ^ (m + 1))), ∃ c : Γ(B.X, ⊤), g = γ ^ p ^ m * c := by
  first | exact @GlobalTheory.ChainParts.dvd_of_isRootOfP_pow_succ | exact GlobalTheory.ChainParts.dvd_of_isRootOfP_pow_succ | (intros; apply GlobalTheory.ChainParts.dvd_of_isRootOfP_pow_succ <;> assumption)
