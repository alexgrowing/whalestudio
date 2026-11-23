import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentProjectionVectorBundleRank
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
theorem _root_.GlobalTheory.T.idempotent_projection_vector_bundle_rank : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a) (P : EPres B Λ), ∃ r, GlobalTheory.VB.IsVB ((partF c a).obj P.E) r ∧ GlobalTheory.VB.IsVB ((partF c a).obj P.E') r ∧
      IsIso (B.genRes.map ((partF c a).map P.ψ)) := by
  first | exact @GlobalTheory.ChainParts.PartVB.main | exact GlobalTheory.ChainParts.PartVB.main | (intros; apply GlobalTheory.ChainParts.PartVB.main <;> assumption)
