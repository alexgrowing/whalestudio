import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilTranslationActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLeviTranslationIdentity

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.UnipCone

theorem mat_mulVec_of_mem_unip {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) {g : UA σ W.J} (hg : g ∈ unip σ W H') :
    mat g *ᵥ incV F H'.x = incV F H'.x := by
  let S : Subgroup (UA σ W.J) :=
    { carrier := {g | mat g *ᵥ incV F H'.x = incV F H'.x}
      one_mem' := by
        show mat (1 : UA σ W.J) *ᵥ _ = _
        rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
      mul_mem' := by
        intro g h hg hh
        show mat (g * h) *ᵥ _ = _
        rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, show mat h *ᵥ incV F H'.x = incV F H'.x from hh]
        exact hg
      inv_mem' := by
        intro g hg
        show mat g⁻¹ *ᵥ _ = _
        have hg' : mat g *ᵥ incV F H'.x = incV F H'.x := hg
        conv_lhs => rw [← hg']
        rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec] }
  have hle : unip σ W H' ≤ S := (Subgroup.closure_le S).2 fun g hg => hg.1
  exact hle hg

theorem shiftB_mul_transpose {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n n₁ d d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (l : (AE F E)ˣ)
    (M : Matrix (Fin d) (Fin d) (AE F E)) (hM : M *ᵥ incV F H'.x = incV F H'.x) :
    shiftB σ H H' l * Mᵀ = shiftB σ H H' l := by
  rw [shiftB, Matrix.smul_mul, GlobalTheory.ThK.EvLawA.vecMulVec_mul_transpose, hM]

end GlobalTheory.ThK.LemF.UnipCone

end

open GlobalTheory.ThK.LemF.UnipCone GlobalTheory.ThK.EvLawA in

theorem GlobalTheory.ThK.LemF.coneFin_unipB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      ∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ := by
  intro hPr F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev ei' ev' hloc K hK X om om' om₁ om₁' T T₁ v μK μ _ _ u hu huv φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have P' : IsPair B G.M' X.α (X.α / X.β) om' G.q (b + 2 - G.q) _ _ :=
    ⟨T.base, T.geo.hV', T.geo.hW, T.geo.hM', T.chars.heckeα, isHecke_div' T.chars.heckeα T.chars.heckeβ,
      T.chars.resα, by rw [Nat.add_comm]; exact resEtaPow_div' T.chars.resα T.chars.resβ, T.weil'⟩

  have hlaw : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' (om' (1, u) Φ) = (1 : ℂ) • id (e' Φ) := by
    intro Φ hΦ
    have hL : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, Units.val_one, one_smul]
      · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul]
      · rw [GlobalTheory.StabHaar.mat_one, GlobalTheory.StabHaar.mat_one, Matrix.one_mul, Matrix.mul_one]
    have h := GlobalTheory.T.config_b_levi_torus_evaluation hPr F E σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁ 1 1 1 hL u hu Φ hΦ
    simp only [mul_one, Prod.mk_one_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one,
      Module.End.one_apply] at h
    rw [h, id]
  have hevB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v (locOp v (om' (1, u)) ψ) = ev' v ψ := by
    intro ψ hψ
    have hψ₁ : ev' v ψ ∈ SB (Fin b × Fin (a + b) → Fv F v) := by
      rw [← (hloc.2.1 v).2]
      exact Submodule.mem_map_of_mem hψ
    have h := GlobalTheory.T.local_part_operator_unitary_compatible B G.M' G₁.M' T.geo.hM' T₁.geo.hM' e' ei' ev' hloc v (om' (1, u)) id 1 hlaw ψ
      (locOp v (om' (1, u)) ψ) (ev' v ψ) hψ (locOp_mem _ _ _) hψ₁
      (acts_locOp_om hA P' (UAtSub σ G.V' (evFin F v)).one_mem huv hψ) (fun r _ => rfl)
    rw [h, one_smul]

  have key : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ l : (AE F E)ˣ,
      ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) (locOp v (om' (1, u)) φ))) =
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) φ)) := by
    intro k hk l
    rw [GlobalTheory.T.local_weil_action_compatible hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ P' v k u hk huv φ hφ]
    rw [GlobalTheory.T.local_weil_translation_action hPr F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ P' v u huv _ (at_partFin v _) _ (locOp_mem _ _ _)]
    have hfix : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := mat_mulVec_of_mem_unip H' (inv_mem hu)
    rw [partFin, Matrix.smul_mul, shiftB_mul_transpose H H' l _ hfix, ← partFin]
    exact hevB _ (locOp_mem _ _ _)
  funext y
  unfold coneFin
  congr 1
  funext k
  congr 1
  funext l
  unfold coneFinInt
  rw [key k.1 (mem_KAt.1 k.2).2 l.1]
