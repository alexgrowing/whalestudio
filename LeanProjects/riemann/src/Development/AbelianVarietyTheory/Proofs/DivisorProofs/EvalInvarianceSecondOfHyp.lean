import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBUnipotentEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviEvaluationIdentityStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF

namespace GlobalTheory.ThK.EvInvBPf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro u _
  simp [mat]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_small {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

end GlobalTheory.ThK.EvInvBPf

open GlobalTheory.ThK.EvInvBPf in

theorem GlobalTheory.ThK.LemF.evInvB_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → EvInvB := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v l hlinv
  have hA := GlobalTheory.T.theta_action_exists hP
  have hp := hA F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ (isPair_small hT) v
  have hp₁ := hA F E σ B _ _ G₁.V' G₁.W G₁.M' _ _ om₁' _ _ _ _ (isPair_small hT₁) v
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hid : ∀ φ ∈ SB (Fin b × Fin (a + b) → Fv F v), ∃ φ₁ ∈ SB (Fin b × Fin (a + b) → Fv F v),
      Acts (evFin F v) (id : Fn F b (a + b) → Fn F b (a + b)) φ φ₁ :=
    fun φ hφ => ⟨φ, hφ, fun _ _ => rfl⟩
  have hmem : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v φ ∈ SB (Fin b × Fin (a + b) → Fv F v) :=
    fun φ hφ => (hl.2.1 v).2 ▸ Submodule.mem_map_of_mem hφ
  refine ⟨fun u hu huv φ hφ => ?_, fun g₀ g hL hg hg₀ φ hφ => ?_⟩
  · have key := GlobalTheory.T.local_part_operator_compatible F E σ B.ψ _ _ _ _ G.V' G.W G₁.V' G₁.W G.M' G₁.M' hM hM₁ e' ei' ev' hl v (om' (u, 1)) id
      (fun Φ hΦ => GlobalTheory.T.config_b_unipotent_evaluation hP F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ u hu Φ hΦ)
      (fun φ hφ => ((hp.1 u huv 1 (one_mem_UAt _ v) φ hφ).exists))
      hid φ hφ
    rw [key, locOp_of_fix (T := id) (fun _ _ => rfl) (hmem φ hφ)]
  · have key := GlobalTheory.T.local_part_operator_compatible F E σ B.ψ _ _ _ _ G.V' G.W G₁.V' G₁.W G.M' G₁.M' hM hM₁ e' ei' ev' hl v (om' (g, 1)) (om₁' (g₀, 1))
      (fun Φ hΦ => GlobalTheory.T.config_b_levi_evaluation_identity hP F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ g₀ g hL Φ hΦ)
      (fun φ hφ => ((hp.1 g hg 1 (one_mem_UAt _ v) φ hφ).exists))
      (fun φ hφ => ((hp₁.1 g₀ hg₀ 1 (one_mem_UAt _ v) φ hφ).exists)) φ hφ
    rw [key, hlinv g₀ hg₀ _ (hmem φ hφ)]
