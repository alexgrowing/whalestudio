import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeLin
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLocalPartCaseBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleLocalPartCaseBThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleLocalPartCaseBFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseBStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem locOp_comp (hA : ActsEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {v : Pl F} {g k : UA σ X.J}
    (hg : g ∈ UAt σ X (evFin F v)) (hk : k ∈ UAt σ X (evFin F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    locOp v (om (k, 1)) (locOp v (om (g, 1)) φ) = locOp v (om (k * g, 1)) φ := by
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  have hkg : k * g ∈ UAt σ X (evFin F v) := (UAtSub σ X (evFin F v)).mul_mem hk hg
  have hψ₁ : locOp v (om (g, 1)) φ ∈ SB _ := locOp_mem v _ φ
  have a1 := acts_locOp_om hA hP hg h1 hφ
  have a2 := acts_locOp_om hA hP hk h1 hψ₁
  have a3 := acts_locOp_om hA hP hkg h1 hφ
  obtain ⟨r, h0, hr⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have key : tens (evFin F v) (locOp v (om (k, 1)) (locOp v (om (g, 1)) φ)) r =
      tens (evFin F v) (locOp v (om (k * g, 1)) φ) r := by
    rw [← a2 r (hr _ hψ₁), ← a1 r (hr _ hφ), ← a3 r (hr _ hφ)]
    rw [show ((k * g, (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) = (k, 1) * (g, 1) by simp, map_mul]
    rfl
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrz : r (fun i => GlobalTheory.LatVac.liftV v (t i)) = r 0 := by simpa using (hr φ hφ).1 0 _ hz
  have e := congrFun key fun i => GlobalTheory.LatVac.liftV v (t i)
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hrz] at e
  exact mul_right_cancel₀ h0 e

theorem coneLin_locOp (hA : ActsEx) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {v : Pl F}
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (μ : Measure (idelesAt E (evFin F v)))
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)
    (l : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {g k : UA σ X.J}
    (hg : g ∈ UAt σ X (evFin F v)) (hk : k ∈ UAt σ X (evFin F v)) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    coneLin B M om v ev μ u ν z l (locOp v (om (g, 1)) φ) k = coneLin B M om v ev μ u ν z l φ (k * g) := by
  unfold coneLin
  rw [locOp_comp hA hP hg hk hφ]

theorem coneLin_smooth (hA : ActsEx) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') {v : Pl F}
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (μ : Measure (idelesAt E (evFin F v)))
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)
    (l : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ∃ U ∈ 𝓝 (1 : UA σ X.J), ∀ g ∈ UAt σ X (evFin F v), ∀ x ∈ U, x ∈ UAt σ X (evFin F v) →
      coneLin B M om v ev μ u ν z l φ (g * x) = coneLin B M om v ev μ u ν z l φ g := by
  obtain ⟨U, hU, hfix⟩ := (hA F E σ B n d X W M χX χW om r s r' s' hP v).2.2 φ hφ
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).one_mem
  have hc : Continuous fun g : UA σ X.J => ((g, (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) :=
    continuous_id.prodMk continuous_const
  refine ⟨(fun g : UA σ X.J => ((g, (1 : UA σ W.J)) : UA σ X.J × UA σ W.J)) ⁻¹' U,
    hc.continuousAt.preimage_mem_nhds (show U ∈ 𝓝 ((1 : UA σ X.J), (1 : UA σ W.J)) from hU), fun g hg x hx hxv => ?_⟩
  have hfx : locOp v (om (x, 1)) φ = φ := locOp_eq hφ hφ (hfix (x, 1) hx hxv h1)
  unfold coneLin
  rw [← locOp_comp hA hP hxv hg hφ, hfx]

theorem coneInvB (hPr : GlobalTheory.FunPr.Hypotheses₂) : ConeInvB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hl K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ l hlinv g hg φ hφ
  have hA := GlobalTheory.T.theta_action_exists hPr
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  rw [GlobalTheory.T.stabilizer_local_part_case_b hPr F E σ B a b G G₁ H H' hC e' he' ei' ev' hl K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ l _ (locOp_mem _ _ _),
    GlobalTheory.T.stabilizer_local_part_case_b hPr F E σ B a b G G₁ H H' hC e' he' ei' ev' hl K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ l φ hφ]
  have e : ∀ k : KAt K (evFin F v),
      coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l (locOp v (om' (g, 1)) φ) k.1 =
        coneLin B G.M' om' v (ev' v) μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) l φ (k.1 * g) := fun k =>
    coneLin_locOp hA hP' _ _ _ _ _ l hg (mem_KAt.1 k.2).2 hφ
  simp_rw [e]
  exact GlobalTheory.T.stabilizer_haar_local_factor_case_b hPr F E σ B a b G G₁ H H' hC K hK X om om' om₁ om₁' hT hT₁ v μK hμK _
    (coneLin_smooth hA hP' _ _ _ _ _ l hφ)
    (GlobalTheory.T.theta_triple_local_part_case_b_third hPr F E σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v μ hμ l hlinv φ hφ)
    (GlobalTheory.T.theta_triple_local_part_case_b_fourth hPr F E σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v μ hμ l hlinv φ hφ) g hg

end GlobalTheory.ThK.LemF
