import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactFunctorEquivariantChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEmbeddingDualBasisExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentDecompositionDualBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentProjectionFunctorLinearExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentProjectionVectorBundleRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFrobeniusLiftCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfPDivisibilityNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalModelBasisEmbeddingDecompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalModelEmbeddingDecompUniqueStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts
open scoped Classical

namespace GlobalTheory.ChainParts

theorem exists_chain_parts {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    [CharZero O] [CharP (ResidueField O) p] {B : Vert.Model O} (hB : GlobalTheory.IsNormalScheme B.X) {Λ : Type} [CommRing Λ]
    {o : ℕ} (Q : EqChain p B Λ o) {ι : Type} [Finite ι] [DecidableEq ι] (φ : ι → ι) {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (ev : ι → (Λ →+* O)) (cf : ι → Fin n → O) (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0)
    (hn : Nat.card ι = n) (hfr : ∀ τ k, ∃ v : O, cf (φ τ) k = cf τ k ^ p + p * v) :
    ∃ Ch : Chain p B φ o, ∀ τ,
      (∃ r vb vb' iso, Ch.lw τ = ⟨r, (partF (fun k => B.const (cf τ k)) b).obj Q.lw.E,
        (partF (fun k => B.const (cf τ k)) b).obj Q.lw.E', vb, vb', (partF (fun k => B.const (cf τ k)) b).map Q.lw.ψ, iso⟩) ∧
      (∃ r vb vb' iso, Ch.oo τ = ⟨r, (partF (fun k => B.const (cf τ k)) b).obj Q.oo.E,
        (partF (fun k => B.const (cf τ k)) b).obj Q.oo.E', vb, vb', (partF (fun k => B.const (cf τ k)) b).map Q.oo.ψ, iso⟩) := by
  haveI : Fintype ι := Fintype.ofFinite _
  have hcard' : Fintype.card ι = n := by rw [← Nat.card_eq_fintype_card]; exact hn
  have hidem : ∀ τ (M : AM B Λ), IsAdd M →
      eA M (fun k => B.const (cf τ k)) b ≫ eA M (fun k => B.const (cf τ k)) b = eA M (fun k => B.const (cf τ k)) b :=
    fun τ M hM => GlobalTheory.T.idempotent_decomposition_dual_basis b ev cf hev hcard' τ M hM
  have hP := fun τ => GlobalTheory.T.idempotent_projection_functor_linear_exact (fun k => B.const (cf τ k)) b (hidem τ)
  have hc : ∀ τ k, ∃ v : Γ(B.X, ⊤), B.const (cf (φ τ) k) = B.const (cf τ k) ^ p + p * v := fun τ k =>
    (hfr τ k).elim fun v e => ⟨B.const v, by rw [e]; simp only [Model.const, map_add, map_pow, map_mul, map_natCast]⟩
  obtain ⟨Ch, -, -, hCh⟩ := GlobalTheory.T.exact_functor_equivariant_chain p Q φ (fun τ => partF (fun k => B.const (cf τ k)) b)
    (fun τ M g _ => (hP τ).1 M g) (fun τ => (hP τ).2.1) (fun τ _ _ f hM hN => (hP τ).2.2.1 f hM hN)
    (fun τ E => GlobalTheory.T.idempotent_projection_vector_bundle_rank (fun k => B.const (cf τ k)) b (hidem τ) E)
    (fun τ M hM => GlobalTheory.T.idempotent_frobenius_lift_compat p Q.hp (fun k => B.const (cf τ k)) (fun k => B.const (cf (φ τ) k)) b
      (hc τ) (hidem τ) M hM)
    (fun τ => (hP τ).2.2.2) (fun m hm => GlobalTheory.T.root_of_p_divisibility_normal_model p hB Q.g (Q.γ m) m Q.g_root (Q.γ_root m hm))
  exact ⟨Ch, hCh⟩

set_option maxHeartbeats 800000 in

theorem chainPtsSt_of_eqChainSt : EqChainSt → ChainPtsSt := fun hE D O hO p _ _ hun _ W hW jc hjc z o c =>
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  (GlobalTheory.T.unramified_embedding_dual_basis_exists z jc hjc hun).elim fun n h => h.elim fun b h => h.elim fun ev h => h.elim fun cf h =>
  (hE D O hO p W hW jc hjc z o c).elim fun B k => k.elim fun f k => k.elim fun Q k =>
  haveI := h.1
  (exists_chain_parts p k.1 Q (phiPow D 1) b ev cf h.2.2.2.2.1 h.2.1 h.2.2.2.2.2).elim fun Ch hCh =>
  ⟨B, f, Ch, k.1, k.2.1, fun τ =>
    ⟨(hCh τ).1.elim fun r e => e.elim fun vb e => e.elim fun vb' e => e.elim fun iso e =>
      e.symm ▸ GlobalTheory.T.vertical_model_basis_embedding_decomp z jc c B f n b ev cf h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 Q.lw k.2.2.1 τ r vb vb' iso,
     (hCh τ).2.elim fun r e => e.elim fun vb e => e.elim fun vb' e => e.elim fun iso e =>
      e.symm ▸ GlobalTheory.T.vertical_model_embedding_decomp_unique z jc c B f n b ev cf h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 Q.oo k.2.2.2 τ r vb vb' iso⟩⟩

end GlobalTheory.ChainParts

end
