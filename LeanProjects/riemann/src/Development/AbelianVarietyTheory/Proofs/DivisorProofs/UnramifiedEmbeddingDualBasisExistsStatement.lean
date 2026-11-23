import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEmbeddingDualBasisExists
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
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_embedding_dual_basis_exists : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (hjc : Pin W jc) (hun : UnramE D p), ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (𝓞 D.host.E)) (ev : Emb D p → (𝓞 D.host.E →+* z.Z.i.c.V W))
      (cf : Emb D p → Fin n → z.Z.i.c.V W),
      Finite (Emb D p) ∧ Nat.card (Emb D p) = n ∧
      (∀ σ x, ((ev σ x : z.Z.i.c.V W) : z.Z.i.c.F) = embK z.Z.i.c (jc.comp σ) x) ∧
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) ∧
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) ∧
      (∀ τ k, ∃ v : z.Z.i.c.V W, cf (phiPow D 1 τ) k = cf τ k ^ p + p * v) := by
  first | exact @GlobalTheory.IdemCoef.exists_coef | exact GlobalTheory.IdemCoef.exists_coef | (intros; apply GlobalTheory.IdemCoef.exists_coef <;> assumption)
