import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalModelBasisEmbeddingDecomp
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
theorem _root_.GlobalTheory.T.vertical_model_basis_embedding_decomp : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ), haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
    ∀ (c : (nmodel z.Z).Comp) (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c)) (n : ℕ)
      (b : Fin n → 𝓞 D.host.E) (ev : Emb D p → (𝓞 D.host.E →+* z.Z.i.c.V W)) (cf : Emb D p → Fin n → z.Z.i.c.V W),
      (∀ σ x, ((ev σ x : z.Z.i.c.V W) : z.Z.i.c.F) = embK z.Z.i.c (jc.comp σ) x) →
      (∀ σ' : D.host.E →+* ℂ, ∃ σ : Emb D p, σ' = jc.comp σ) →
      (∀ τ σ : Emb D p, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) →
      ∀ P : EPres B (𝓞 D.host.E), IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) false P →
      ∀ (τ : Emb D p) (r : ℕ) vb vb' iso, IsLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xLie S jc τ) false
        ⟨r, (partF (fun k => B.const (cf τ k)) b).obj P.E, (partF (fun k => B.const (cf τ k)) b).obj P.E', vb, vb',
          (partF (fun k => B.const (cf τ k)) b).map P.ψ, iso⟩ := by
  first | exact @GlobalTheory.ChainParts.LatPart.isLatPres_xLie | exact GlobalTheory.ChainParts.LatPart.isLatPres_xLie | (intros; apply GlobalTheory.ChainParts.LatPart.isLatPres_xLie <;> assumption)
