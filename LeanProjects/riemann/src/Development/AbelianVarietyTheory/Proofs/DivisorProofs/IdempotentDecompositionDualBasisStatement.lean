import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentDecompositionDualBasis
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
theorem _root_.GlobalTheory.T.idempotent_decomposition_dual_basis : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {R : Type} [CommRing R] [Algebra R Γ(B.X, ⊤)] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R) (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι) (M : AM B Λ) (hM : IsAdd M), eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b ≫ eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b =
      eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b := by
  first | exact @GlobalTheory.ChainParts.eA_idem | exact GlobalTheory.ChainParts.eA_idem | (intros; apply GlobalTheory.ChainParts.eA_idem <;> assumption)
