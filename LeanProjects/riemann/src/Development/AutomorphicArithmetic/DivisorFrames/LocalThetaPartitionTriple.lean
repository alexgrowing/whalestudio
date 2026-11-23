import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationIsoBTriplePair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section SlopeTestRemainingChoices

open Matrix GlobalTheory.LocPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem hTens_uS {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ d d₁ : ℕ} (JA : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin d) (Fin d) E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t s : Fv F v ⊗[F] E) :
    GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) (GlobalTheory.VanishLoc.uAt H H' v t) (uS σ H H' v s) =
      GlobalTheory.VanishLoc.liftT v t * GlobalTheory.VanishLoc.liftT v s * inclR (F := F) (AF F) (form σ JA H.x H.y) *
        inclR (F := F) (AF F) (form σ JB H'.y H'.x) := by
  simp only [GlobalTheory.WeilM.hTens, GlobalTheory.VanishLoc.uAt, uS, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
    incV, incM, Matrix.map_apply, smul_eq_mul, map_mul, cA_inclR, cA_cA hσ, form, dotProduct, Matrix.mulVec,
    map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_)
  ring

private theorem pair_uS {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (hC : CfgB B G G₁ H H') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (hT : IsTriple B G X om om')
    (v : Pl F) (t s : Fv F v ⊗[F] E) :
    (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (uS σ H H' v s)).2 -
                 (GlobalTheory.LatVac.locCo G.M'.co v (uS σ H H' v s)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).2 =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hT.base.cm.2.2.1]; norm_num)
  have hσ := cm_conj_conj hT.base.cm
  have hxy : form σ G.V'.J H.x H.y = 1 := hC.hH.xy
  have hyx : form σ G.W.J H'.y H'.x = -1 := by
    rw [form_swap_skew hσ _ hT.geo.hW.skew, hC.hH'.xy, map_one]
  rw [locCo_pair, GlobalTheory.WeilM.symp, hTens_uS hσ, evFin_trace, hxy, hyx, map_one, map_neg, map_one]
  have e : (-1 : AE F E) * (GlobalTheory.VanishLoc.liftT v t * GlobalTheory.VanishLoc.liftT v s * 1 * -1) =
      GlobalTheory.VanishLoc.liftT v t * GlobalTheory.VanishLoc.liftT v s := by ring
  rw [e, map_mul, compFin_liftT, compFin_liftT]

end SlopeTestRemainingChoices

theorem UpperTheory.local_theta_partition_triple :
    GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
                 (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
                 ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
                 ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∀ t s : Fv F v ⊗[F] E,
                   evS B G.M' v (ev' v) H H' (locOp v (G.M'.co.rho B.ψ (partFin v (GlobalTheory.VanishLoc.uAt H H' v t))) φ) s =
                     GlobalTheory.LatVac.psiAt B.ψ v (-Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * s)) • evS B G.M' v (ev' v) H H' φ s := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE ei ev hL X om om' om₁ om₁' hT hT₁ v φ hφ t s
  obtain ⟨hei, hvac, hfac⟩ := hL
  have hψ : Continuous B.ψ := hT.base.std.1
  have hU := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)) φ hφ
  have hS := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v (uS σ H H' v s)) φ hφ
  have h1 := GlobalTheory.VanishLocInv.inv_local B G G₁ H H' e' hE X om om' om₁ om₁' hT hT₁ ei ev hei hvac hfac v
    (GlobalTheory.VanishLoc.uAt H H' v t) (GlobalTheory.VanishLoc.uAt_mem_isoB H H' v t) (GlobalTheory.VanishLoc.at_uAt H H' v t) _ hS
  rw [evS, evS, (locOp_rho G.M'.co hψ v (GlobalTheory.VanishLoc.uAt H H' v t) hφ).2,
    (locOp_rho G.M'.co hψ v (uS σ H H' v s) hU).2, (locOp_rho G.M'.co hψ v (uS σ H H' v s) hφ).2,
    GlobalTheory.VanishLoc.schr_comm, map_smul, h1, ← pair_uS B G G₁ H H' hC X om om' hT v t s, neg_sub]
