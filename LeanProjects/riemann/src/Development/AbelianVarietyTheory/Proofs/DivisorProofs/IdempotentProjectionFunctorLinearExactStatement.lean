import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentProjectionFunctorLinearExact
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
theorem _root_.GlobalTheory.T.idempotent_projection_functor_linear_exact : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (hidem : ∀ M : AM B Λ, IsAdd M → eA M c a ≫ eA M c a = eA M c a), (∀ (M : AM B Λ) (g : Γ(B.X, ⊤)), (partF c a).map (smulA M g) = smulHom ((partF c a).obj M) g) ∧
    (∀ S : ShortComplex (AM B Λ), S.ShortExact → IsAdd S.X₁ → IsAdd S.X₂ → IsAdd S.X₃ →
      (S.map (partF c a)).ShortExact) ∧
    (∀ {M N : AM B Λ} (f : M ⟶ N), IsAdd M → IsAdd N →
      Nonempty ((partF c a).obj (cokernel f) ≅ cokernel ((partF c a).map f))) ∧
    (∀ M : AM B Λ, IsAdd M → ∃ (i : (partF c a).obj M ⟶ M.V) (q : M.V ⟶ (partF c a).obj M), i ≫ q = 𝟙 _) := by
  first | exact @GlobalTheory.ChainParts.partF_exact | exact GlobalTheory.ChainParts.partF_exact | (intros; apply GlobalTheory.ChainParts.partF_exact <;> assumption)
