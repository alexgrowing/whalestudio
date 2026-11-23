import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFrobeniusLiftCompat
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
theorem _root_.GlobalTheory.T.idempotent_frobenius_lift_compat : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ] (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {n : ℕ} (c c' : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hc : ∀ k, ∃ v : Γ(B.X, ⊤), c' k = c k ^ p + p * v) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a) (M : AM B Λ) (hM : IsAdd M), Nonempty ((partF c' a).obj (frobA p h M) ≅ (frobFun p h).obj ((partF c a).obj M)) := by
  first | exact @GlobalTheory.ChainParts.FrobPart.main | exact GlobalTheory.ChainParts.FrobPart.main | (intros; apply GlobalTheory.ChainParts.FrobPart.main <;> assumption)
