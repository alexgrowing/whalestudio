import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactAction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockVectorsKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactActionStatement

section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLine
section Abstract
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
end Abstract
end GlobalTheory.KExpLine
namespace GlobalTheory.KExpLine
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
theorem sub_mem_span_kInfty_exp_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f hf f₁ hact
  obtain ⟨hDer, hOp, -, -⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨γ, hγL, hγ1, hγK⟩ := GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact F E σ B n X r s hP.base hP.herm k hk
  obtain ⟨S, hSfin, hS⟩ := _root_.GlobalTheory.T.fock_vectors_kFinite hPr F E σ B n d X W M χX χW om r s r' s' hP f hf
  haveI := hSfin
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let c : ℝ → SInf F (Fin n × Fin d) := fun t => D t f
  have hcP : ∀ t, c t ∈ M.Pol B.ψ B.emb := fun t => hDP t f hf
  have hcA : ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (c t) := fun t => (hD t f hf (c t)).2 rfl
  have hc1 : c 1 = f₁ := ((hD 1 f hf f₁).1 (by rw [hγ1]; exact hact)).symm
  have hc0 : c 0 = f := by
    have h1 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one]
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd (0 : ℝ)), 1)) f f := by
      intro ρ _
      rw [h1]
      show om 1 _ = _
      rw [map_one]
      rfl
    exact ((hD 0 f hf f).1 hA).symm
  have hder : ∀ y t, HasDerivAt (fun u => c u y) (Dg (c t) y) t := by
    intro y t
    let ρ := GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)
    let x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (y, 0)
    have hx : (fun i => evI F (x i)) = y := funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv _ _ i
    have hρ : ρ x = 1 := by
      show GlobalTheory.ArchIsom.g0 F (Fin n × Fin d) (fun i => (x i).2) = 1
      have : (fun i => (x i).2) = (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := rfl
      rw [this]
      exact Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts _) _
    have htens : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) ρ x = g y := by
      intro g
      show g (fun i => evI F (x i)) * ρ x = g y
      rw [hx, hρ, mul_one]
    have hom : ∀ u, om (γ (Multiplicative.ofAdd u), 1) (tens (evI F) (⇑f) ρ) = tens (evI F) (⇑(c u)) ρ :=
      fun u => hcA u ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)
    have hsplit : ∀ s', om (γ (Multiplicative.ofAdd (s' + t)), 1) (tens (evI F) (⇑f) ρ) =
        om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) := by
      intro s'
      have e : ((γ (Multiplicative.ofAdd (s' + t)), (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) =
          (γ (Multiplicative.ofAdd s'), 1) * (γ (Multiplicative.ofAdd t), 1) := by
        rw [ofAdd_add, map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, map_mul, Module.End.mul_apply, hom t]
    have h0 := (hDg (c t) (hcP t) (Dg (c t))).2 rfl ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ (c t)) x
    have h0' : HasDerivAt (fun s' => c (s' + t) y) (Dg (c t) y) 0 := by
      have e1 : (fun s' : ℝ => om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) x) =
          fun s' => c (s' + t) y := by
        funext s'
        rw [← hsplit s', hom, htens]
      rw [e1, htens] at h0
      exact h0
    have h2' : HasDerivAt (fun u => c (u - t + t) y) (Dg (c t) y) t := by
      have := h0'
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
      exact this.comp_sub_const t t
    simpa only [sub_add_cancel] using h2'
  rw [← hc1, ← hc0]
  refine sub_mem_of_hasDerivAt S _ c (fun t => Dg (c t)) (fun u => hS _ (hγK _) (c u) (hcA u)) (fun t => ?_) hder
  exact Submodule.subset_span ⟨hDgP _ (hcP t), γ, hγL, c t, hcP t, (hDg (c t) (hcP t) _).2 rfl⟩
end GlobalTheory.KExpLine
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfty_exponential_line_in_derivative_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  first | exact @_root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | exact _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | (intros; apply _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives <;> assumption)
end
