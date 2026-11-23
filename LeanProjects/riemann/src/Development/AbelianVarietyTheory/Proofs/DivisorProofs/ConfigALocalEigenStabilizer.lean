import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartEvalStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPrintsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementLocalIdeleExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeALocalPartTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeALocalPartStabilizerStatement

noncomputable section

namespace GlobalTheory.ConeLeviInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

theorem cone_as_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∃ m : (AE F E)ˣ → UA σ G.V.J,
      (∀ t ∈ idelesAt E (evFin F v), IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v)) ∧
      ∀ (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          coneEvFun B G H H' om v (ev v) l φ ((m p.2.1)⁻¹ * p.1.1) * ((absE F E p.2.1 : ℝ) : ℂ) ^ (b + 1)) (μK.prod μ) ∧
        l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
          ∫ k, ∫ t, coneEvFun B G H H' om v (ev v) l φ ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e hE ei ev hL K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  obtain ⟨m, hm⟩ := GlobalTheory.T.levi_element_local_idele_exists F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  refine ⟨m, hm, fun l φ hφ => ?_⟩
  have hPr := Inhab.pairV hT
  have hMul := GlobalTheory.T.local_operator_mul_of_classicalTheorems hP F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hPr v
  have hone : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), locOp v (om 1) ψ = ψ := fun ψ hψ =>
    locOp_of_fix (fun Φ _ => by rw [map_one]; rfl) hψ
  have hone₁ : ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), locOp v (om₁ 1) ψ = ψ := fun ψ hψ =>
    locOp_of_fix (fun Φ _ => by rw [map_one]; rfl) hψ
  have hevSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v ψ ∈ SB (Fin b × Fin (b + a') → Fv F v) :=
    fun ψ hψ => (hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := one_mem (UAtSub σ G.W (evFin F v))
  have h1V₁ : (1 : UA σ G₁.V.J) ∈ UAt σ G₁.V (evFin F v) := one_mem (UAtSub σ G₁.V (evFin F v))

  have hshift : ∀ t ∈ idelesAt E (evFin F v), ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' t))) ψ) =
        fac (X.β / X.α) (((b + a' : ℕ) : ℝ) / 2) t •
          ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) (locOp v (om ((m t)⁻¹, 1)) ψ)) := by
    intro t ht ψ hψ
    obtain ⟨hlev, hmv⟩ := hm t ht
    have hmv' : (m t)⁻¹ ∈ UAt σ G.V (evFin F v) := inv_mem (show m t ∈ UAtSub σ G.V (evFin F v) from hmv)
    have hback : locOp v (om (m t, 1)) (locOp v (om ((m t)⁻¹, 1)) ψ) = ψ := by
      rw [← hMul (m t, 1) ((m t)⁻¹, 1) hmv h1W hmv' h1W ψ hψ, Prod.mk_mul_mk, mul_inv_cancel, mul_one,
        Prod.mk_one_one, hone ψ hψ]
    have hc := GlobalTheory.T.local_weil_action_compatibility hP F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hPr v (m t) 1 hmv h1W (shiftA H H' 1)
      (locOp v (om ((m t)⁻¹, 1)) ψ) (locOp_mem _ _ _)
    have hc2 : locOp v (om (m t, 1)) (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1)))
        (locOp v (om ((m t)⁻¹, 1)) ψ)) = locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' t))) ψ := by
      rw [hc, hback]
      refine congrArg (fun w => locOp v (G.M.co.rho B.ψ (partFin v w)) ψ) ?_
      ext i j
      change ∑ k, (∑ l, mat (m t) i l * shiftA H H' 1 l k) * (mat (1 : UA σ G.W.J))ᵀ k j = shiftA H H' t i j
      rw [GlobalTheory.StabHaar.mat_one]
      simp only [Matrix.transpose_one, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      simp only [shiftA, Matrix.smul_apply, Matrix.vecMulVec_apply, Units.val_one, one_smul, smul_eq_mul]
      have h := congrFun hlev.1 i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
      rw [← mul_assoc, ← h, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← hc2, GlobalTheory.T.seesaw_type_a_local_part_triple hP F E σ B b a' G G₁ H H' hC e hE ei ev hL X om om' om₁ om₁' hT hT₁ v t 1 (m t) hlev hmv h1V₁ _
      (locOp_mem _ _ _), Prod.mk_one_one, hone₁ _ (hevSB _ (locOp_mem _ _ _))]

  obtain ⟨hlt, hev⟩ := (⟨hT.geo.lt, hT.geo.even⟩ : a' < b + 2 ∧ Even (b + 2 + a'))
  obtain ⟨r, hr⟩ := hev
  have hexp : (((b + a' : ℕ) : ℝ) / 2) = (((b + a') / 2 : ℕ) : ℝ) := by
    rw [show (b + a') / 2 = r - 1 by omega, show b + a' = 2 * (r - 1) by omega]
    push_cast
    ring
  have hsum : (b + a') / 2 + (b + 2 - a') / 2 = b + 1 := by omega

  have hpt : ∀ (k : KAt K (evFin F v)) (t : idelesAt E (evFin F v)),
      l (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' t.1))) (locOp v (om (k.1, 1)) φ))) * (X.ν t.1 : ℂ) *
          ((absE F E t.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) =
        coneEvFun B G H H' om v (ev v) l φ ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) := by
    intro k t
    obtain ⟨hlev, hmv⟩ := hm t.1 t.2
    have hmv' : (m t.1)⁻¹ ∈ UAt σ G.V (evFin F v) := inv_mem (show m t.1 ∈ UAtSub σ G.V (evFin F v) from hmv)
    have hk : k.1 ∈ UAt σ G.V (evFin F v) := (mem_KAt.1 k.2).2
    have hcomp := hMul ((m t.1)⁻¹, 1) (k.1, 1) hmv' h1W hk h1W φ hφ
    rw [Prod.mk_mul_mk, mul_one] at hcomp
    have hχ : ((X.β / X.α) t.1 : ℂ) * (X.ν t.1 : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← MonoidHom.mul_apply, Chars.ν, ← inv_div, inv_mul_cancel, MonoidHom.one_apply,
        Circle.coe_one]
    rw [hshift t.1 t.2 _ (locOp_mem _ _ _), map_smul, smul_eq_mul, coneEvFun, hcomp, fac, hexp, Real.rpow_natCast]
    rw [← hsum, pow_add, Complex.ofReal_pow]
    linear_combination (l (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1)))
      (locOp v (om ((m t.1)⁻¹, 1)) (locOp v (om (k.1, 1)) φ))))) *
      ((absE F E t.1 : ℝ) : ℂ) ^ ((b + a') / 2) * ((absE F E t.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * hχ
  refine ⟨(GlobalTheory.T.seesaw_type_a_local_part_stabilizer hP F E σ B b a' G G₁ H H' hC e hE ei ev hL K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ φ hφ l).congr
    (Eventually.of_forall fun p => hpt p.1 p.2), ?_⟩
  obtain ⟨N, g, c, hg, hsumL⟩ := GlobalTheory.T.local_part_eval_stabilizer hP F E σ B b a' G G₁ H H' hC e hE ei ev hL K hK X om om' om₁ om₁' hT hT₁ v
    μK μ hμK hμ φ hφ
  have h1 : coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ = ∑ i, c i • g i := by
    funext y
    have := hsumL LinearMap.id y
    simp only [LinearMap.id_apply] at this
    simp only [coneFin, coneFinInt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact this
  have h2 := hsumL (l.smulRight (1 : (Fin b × Fin (b + a') → Fv F v) → ℂ)) 0
  simp only [LinearMap.smulRight_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h2
  rw [h1, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← h2]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  exact integral_congr_ae (Eventually.of_forall fun t => hpt k t)

end GlobalTheory.ConeLeviInt

end
