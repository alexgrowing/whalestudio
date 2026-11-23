import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilTranslationActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorUnitaryCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLeviTranslationIdentity

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.LeviPoint

theorem cA_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (y : AE F E) : cA σ (cA σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mat_inv_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (m : UA σ W.J) (t : (AE F E)ˣ) (x : Fin d → AE F E)
    (h : mat m *ᵥ x = (t : AE F E) • x) : mat m⁻¹ *ᵥ x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • x := by
  have h1 : mat m⁻¹ *ᵥ (mat m *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  rw [h, Matrix.mulVec_smul] at h1
  conv_rhs => rw [← h1]
  rw [smul_smul, Units.inv_mul, one_smul]

theorem shiftB_mul_transpose {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ d d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (l s : (AE F E)ˣ)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (hM : M *ᵥ incV F H'.x = (s : AE F E) • incV F H'.x) :
    shiftB σ H H' l * Mᵀ = shiftB σ H H' (l * Units.map (cA σ : AE F E →* AE F E) s) := by
  rw [shiftB, shiftB, Matrix.smul_mul, GlobalTheory.ThK.EvLawA.vecMulVec_mul_transpose, hM, Matrix.vecMulVec_smul, smul_smul,
    Units.val_mul, map_mul, Units.coe_map, MonoidHom.coe_coe, cA_cA hσ]

end GlobalTheory.ThK.LemF.LeviPoint

end

open GlobalTheory.ThK.LemF.LeviPoint in

theorem GlobalTheory.ThK.LemF.leviPointB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) →
      h₁ ∈ UAt σ G₁.W (evFin F v) → ∀ k ∈ UAt σ G.V' (evFin F v), ∀ l : (AE F E)ˣ,
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) (locOp v (om' (1, m)) φ))) =
          fac X.α ((b : ℝ) / 2) t • locOp v (om₁' (1, h₁)) (ev' v (locOp v (G.M'.co.rho B.ψ
            (partFin v (shiftB σ H H' (l * Units.map (cA σ : AE F E →* AE F E) t⁻¹)))) (locOp v (om' (k, 1)) φ))) := by
  intro hPr F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev ei' ev' hloc X om om' om₁ om₁' T T₁ v t h₁ m hL hmv hh₁v k hk l φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have P' := GlobalTheory.ThK.Inhab.pairV' T
  have P₁' := GlobalTheory.ThK.Inhab.pairV' T₁
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.ThK.Inhab.conj_conj T.base.cm
  have hlaw : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      e' (om' (1, m) Φ) = fac X.α ((b : ℝ) / 2) t • om₁' (1, h₁) (e' Φ) := by
    intro Φ hΦ
    have h := GlobalTheory.T.config_b_levi_torus_evaluation hPr F E σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁ t h₁ m hL 1 (one_mem _) Φ hΦ
    rw [one_mul] at h
    exact h
  have hevB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ev' v (locOp v (om' (1, m)) ψ) = fac X.α ((b : ℝ) / 2) t • locOp v (om₁' (1, h₁)) (ev' v ψ) := by
    intro ψ hψ
    have hψ₁ : ev' v ψ ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
      rw [← (hloc.2.1 v).2]
      exact Submodule.mem_map_of_mem hψ
    exact GlobalTheory.ThK.LemF.LocPartLaw.locPart_law B G.M' G₁.M' T.geo.hM' T₁.geo.hM' e' ei' ev' hloc v (om' (1, m)) (om₁' (1, h₁)) _ hlaw ψ
      (locOp v (om' (1, m)) ψ) (locOp v (om₁' (1, h₁)) (ev' v ψ)) hψ (locOp_mem _ _ _) (locOp_mem _ _ _)
      (acts_locOp_om hA P' (UAtSub σ G.V' (evFin F v)).one_mem hmv hψ)
      (acts_locOp_om hA P₁' (UAtSub σ G₁.V' (evFin F v)).one_mem hh₁v hψ₁)
  rw [GlobalTheory.T.local_weil_action_compatible hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ P' v k m hk hmv φ hφ]
  rw [GlobalTheory.T.local_weil_translation_action hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ P' v m hmv _ (at_partFin v _) _ (locOp_mem _ _ _)]
  rw [partFin, Matrix.smul_mul, shiftB_mul_transpose hσ H H' l t⁻¹ _ (mat_inv_mulVec m t _ hL.1), ← partFin]
  exact hevB _ (locOp_mem _ _ _)
