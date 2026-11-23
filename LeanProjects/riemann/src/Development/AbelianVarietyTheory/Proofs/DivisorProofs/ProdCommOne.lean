import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZeroLocalLawOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZeroInfiniteLawOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLawSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLawFirstOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeInvarianceSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeInvarianceFirstOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteInvarianceSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteInvarianceFirstOfPrintsStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

section Derive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev :=
  (UAtSub σ X ev).one_mem

theorem isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) :
    IsLevi H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, Units.val_one, one_smul]
  · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul]
  · rw [GlobalTheory.StabHaar.mat_one, GlobalTheory.StabHaar.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem fac_one (χ : Chr F E) (z : ℝ) : fac χ z 1 = 1 := by
  simp [fac]

theorem locOp_one {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) : locOp v (om (1, 1)) φ = φ :=
  locOp_of_fix (fun Φ _ => by rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]; rfl) hφ

theorem p_locOp_eq (hA : ActsEx) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {v : Pl F} {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P) (hp : augAt om v ≤ LinearMap.ker p)
    {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {ψ : (Fin n × Fin d → Fv F v) → ℂ}
    (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) : p (locOp v (om (g, 1)) ψ) = p ψ := by
  have hact := acts_locOp_om hA hP hg (one_mem_UAt W (evFin F v)) hψ
  have hmem : locOp v (om (g, 1)) ψ - ψ ∈ augAt om v :=
    Submodule.subset_span ⟨g, hg, ψ, hψ, _, locOp_mem v _ ψ, hact, rfl⟩
  have h := hp hmem
  rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at h

theorem prod_one_mul {G₁ G₂ : Type} [Monoid G₁] [Monoid G₂] (u h : G₂) :
    ((1 : G₁), u * h) = ((1 : G₁), u) * (1, h) := by
  rw [Prod.mk_mul_mk, one_mul]

theorem prod_comm_one {G₁ G₂ : Type} [Monoid G₁] [Monoid G₂] (g : G₁) (h : G₂) :
    ((1 : G₁), h) * (g, 1) = (g, (1 : G₂)) * (1, h) := by
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, mul_one, one_mul]

theorem lemFZero_of (hA : ActsEx) (hM : LocOpMul) (hL : EvZeroLocLaw) : LemFZero := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e he ei ev hev v
  have hSB : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ ∈ SB (Fin n × Fin d₁ → Fv F v) := fun ψ hψ =>
    (hev.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ
  have law := hL F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e he ei ev hev v
  have mul := hM F E σ B n d X W M χX χW om r s r' s' hP v
  have h1X := one_mem_UAt (σ := σ) X (evFin F v)
  have h1W := one_mem_UAt (σ := σ) W (evFin F v)
  have h1W₁ := one_mem_UAt (σ := σ) W₁ (evFin F v)
  refine ⟨fun u hu huv h hh φ hφ => ?_, fun t h₁ m hl hm hh₁ h hh φ hφ => ?_,
    fun P₁ _ _ p₁ hp g hg h hh φ hφ => ?_⟩
  · rw [prod_one_mul, mul (1, u) (1, h) h1X huv h1X hh φ hφ]
    have := law 1 h1X 1 1 1 (isLevi_one H') h1W h1W₁ u hu huv (locOp v (om (1, h)) φ) (locOp_mem v _ φ)
    rw [mul_one] at this
    rw [this, fac_one, one_smul, locOp_one om₁ v (hSB _ (locOp_mem v _ φ))]
  · rw [prod_one_mul, mul (1, m) (1, h) h1X hm h1X hh φ hφ]
    have := law 1 h1X t h₁ m hl hm hh₁ 1 (Subgroup.one_mem _) h1W (locOp v (om (1, h)) φ) (locOp_mem v _ φ)
    rwa [one_mul] at this
  · have e3 : locOp v (om (1, h)) (locOp v (om (g, 1)) φ) = locOp v (om (g, 1)) (locOp v (om (1, h)) φ) := by
      rw [← mul (1, h) (g, 1) h1X hh hg h1W φ hφ, ← mul (g, 1) (1, h) hg h1W h1X hh φ hφ, prod_comm_one]
    rw [e3]
    have := law g hg 1 1 1 (isLevi_one H') h1W h1W₁ 1 (Subgroup.one_mem _) h1W (locOp v (om (1, h)) φ) (locOp_mem v _ φ)
    rw [mul_one] at this
    rw [this, fac_one, one_smul, p_locOp_eq hA hP₁ p₁ hp hg (hSB _ (locOp_mem v _ φ))]

theorem lemFConeB_of (hA : ActsEx) (hM : LocOpMul) (hL : ConeLawB) (hI : ConeInvB) : LemFConeB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e' he' ei' ev' hev' K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hP₁' := GlobalTheory.ThK.Inhab.pairV' hT₁
  obtain ⟨hSBc, hU, hLv⟩ := hL F E σ B a b G G₁ H H' hc e' he' ei' ev' hev' K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have mul := hM F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP' v
  have h1X := one_mem_UAt (σ := σ) G.V' (evFin F v)
  have h1W := one_mem_UAt (σ := σ) G.W (evFin F v)
  refine ⟨fun u hu huv h hh φ hφ => ?_, fun t h₁ m hl hm hh₁ h hh φ hφ => ?_,
    fun P₁ _ _ p₁ hp g hg h hh φ hφ => ?_⟩
  · rw [prod_one_mul, mul (1, u) (1, h) h1X huv h1X hh φ hφ]
    exact hU u hu huv _ (locOp_mem v _ φ)
  · rw [prod_one_mul, mul (1, m) (1, h) h1X hm h1X hh φ hφ]
    exact hLv t h₁ m hl hm hh₁ _ (locOp_mem v _ φ)
  · have e3 : locOp v (om' (1, h)) (locOp v (om' (g, 1)) φ) = locOp v (om' (g, 1)) (locOp v (om' (1, h)) φ) := by
      rw [← mul (1, h) (g, 1) h1X hh hg h1W φ hφ, ← mul (g, 1) (1, h) hg h1W h1X hh φ hφ, prod_comm_one]
    rw [e3]
    have key : ∀ f : Module.Dual ℂ P₁, f (p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν
        ((a - (b + 2)) / 2 + 1) (locOp v (om' (g, 1)) (locOp v (om' (1, h)) φ)))) =
        f (p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1)
          (locOp v (om' (1, h)) φ))) := fun f =>
      hI F E σ B a b G G₁ H H' hc e' he' ei' ev' hev' K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ (f ∘ₗ p₁)
        (fun g₀ hg₀ ψ hψ => by rw [LinearMap.comp_apply, LinearMap.comp_apply, p_locOp_eq hA hP₁' p₁ hp hg₀ hψ])
        g hg _ (locOp_mem v _ φ)
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => by rw [map_sub, key f, sub_self])

theorem lemFConeA_of (hA : ActsEx) (hM : LocOpMul) (hL : ConeLawA) (hI : ConeInvA) : LemFConeA := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he ei ev hev K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP₁ := GlobalTheory.ThK.Inhab.pairV hT₁
  obtain ⟨hSBc, hU, hLv⟩ := hL F E σ B b a' G G₁ H H' hc e he ei ev hev K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have mul := hM F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v
  have h1X := one_mem_UAt (σ := σ) G.V (evFin F v)
  have h1W := one_mem_UAt (σ := σ) G.W (evFin F v)
  refine ⟨fun u hu huv h hh φ hφ => ?_, fun t h₁ m hl hm hh₁ h hh φ hφ => ?_,
    fun P₁ _ _ p₁ hp g hg h hh φ hφ => ?_⟩
  · rw [prod_one_mul, mul (1, u) (1, h) h1X huv h1X hh φ hφ]
    exact hU u hu huv _ (locOp_mem v _ φ)
  · rw [prod_one_mul, mul (1, m) (1, h) h1X hm h1X hh φ hφ]
    exact hLv t h₁ m hl hm hh₁ _ (locOp_mem v _ φ)
  · have e3 : locOp v (om (1, h)) (locOp v (om (g, 1)) φ) = locOp v (om (g, 1)) (locOp v (om (1, h)) φ) := by
      rw [← mul (1, h) (g, 1) h1X hh hg h1W φ hφ, ← mul (g, 1) (1, h) hg h1W h1X hh φ hφ, prod_comm_one]
    rw [e3]
    have key : ∀ f : Module.Dual ℂ P₁, f (p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν
        ((b + 2 - a') / 2) (locOp v (om (g, 1)) (locOp v (om (1, h)) φ)))) =
        f (p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2)
          (locOp v (om (1, h)) φ))) := fun f =>
      hI F E σ B b a' G G₁ H H' hc e he ei ev hev K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ (f ∘ₗ p₁)
        (fun g₀ hg₀ ψ hψ => by rw [LinearMap.comp_apply, LinearMap.comp_apply, p_locOp_eq hA hP₁ p₁ hp hg₀ hψ])
        g hg _ (locOp_mem v _ φ)
    exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => by rw [map_sub, key f, sub_self])

end Derive

end GlobalTheory.ThK.LemF

namespace GlobalTheory.ThK.LemF

theorem lemF : GlobalTheory.FunPr.Hypotheses₂ → LocOpMul ∧ EvZeroLocLaw ∧ EvZeroInfLaw ∧ ConeLawB ∧ ConeLawA ∧ ConeInvB ∧ ConeInvA ∧
    EvInvB ∧ EvInvA ∧ InfInvB ∧ InfInvA ∧ LemFZero ∧ LemFConeB ∧ LemFConeA := fun hPr =>
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  ⟨GlobalTheory.T.local_operator_mul_of_classicalTheorems hPr, GlobalTheory.T.eval_zero_local_law_of_hypotheses hPr, GlobalTheory.T.eval_zero_infinite_law_of_hypotheses hPr, GlobalTheory.T.cone_law_second_of_hypotheses hPr, GlobalTheory.T.cone_law_first_of_hypotheses hPr, GlobalTheory.T.cone_invariance_second_of_hypotheses hPr,
    GlobalTheory.T.cone_invariance_first_of_hypotheses hPr, GlobalTheory.T.eval_invariance_second_of_hypotheses hPr, GlobalTheory.T.eval_invariance_first_of_hypotheses hPr, GlobalTheory.T.infinite_invariance_second_of_hypotheses hPr, GlobalTheory.T.infinite_invariance_first_of_hypotheses hPr,
    lemFZero_of hA (GlobalTheory.T.local_operator_mul_of_classicalTheorems hPr) (GlobalTheory.T.eval_zero_local_law_of_hypotheses hPr),
    lemFConeB_of hA (GlobalTheory.T.local_operator_mul_of_classicalTheorems hPr) (GlobalTheory.T.cone_law_second_of_hypotheses hPr) (GlobalTheory.T.cone_invariance_second_of_hypotheses hPr),
    lemFConeA_of hA (GlobalTheory.T.local_operator_mul_of_classicalTheorems hPr) (GlobalTheory.T.cone_law_first_of_hypotheses hPr) (GlobalTheory.T.cone_invariance_first_of_hypotheses hPr)⟩

end GlobalTheory.ThK.LemF

end
