import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.LatticeBasics.PolFin
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsL
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

open UpperTheory.TP

namespace UpperTheory.PolynomialDataFiniteKType₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

private theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

private theorem gInf_le {W : Spc F E d} {k : UA σ W.J} (hk : k ∈ gInf σ W) : k ∈ UAt σ W (evI F) := by
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro u _
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  | mul g h _ _ hg hh =>
    intro u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      have : mat (g * h) = mat g * mat h := rfl
      rw [this, sub_mul, one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  | inv g _ hg =>
    intro u hu
    have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

private noncomputable def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end UpperTheory.PolynomialDataFiniteKType₂

open UpperTheory.PolynomialDataFiniteKType₂ in
theorem UpperTheory.polynomial_data_finite_K_type :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → ∀ Φ ∈ PolData B M, ∃ V : Submodule ℂ (Fn F n d), FiniteDimensional ℂ V ∧ V ≤ schA F (Fin n × Fin d) ∧ ∀ k ∈ gInf σ W, om (1, k) Φ ∈ V := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om hP Φ hΦ
  have hK : ∀ k ∈ gInf σ W, k ∈ KInf σ W B.emb := fun k hk =>
    ⟨gInf_le hk, fun w => by
      rw [GlobalTheory.ThK.Dbl.Prs.cartan_one (hP.skew.sig w) (hP.skew.cartan w)]
      exact Commute.one_right _⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := h2
    have hD : GlobalTheory.ThK.Dbl.Prs.Dat B M hfin.toFinset f φ :=
      ⟨hf, h1, fun v hv => by simpa using hv⟩
    obtain ⟨g, hg, e⟩ := hD.pureA hP.good
    obtain ⟨U, hU, hU'⟩ := polFin hP f hf
    refine ⟨U.map (pureL φ), inferInstance, ?_, fun k hk => ?_⟩
    · rintro _ ⟨f', -, rfl⟩
      exact Submodule.subset_span ⟨f', g, hg, e f'⟩
    · obtain ⟨A, hA⟩ := GlobalTheory.ThK.Dbl.Prs.inf_op PositivityTheory.ThKF.A.archOp hP (hK k hk)
      have hact := (hA f hf).2
      exact ⟨A f, hU' k (hK k hk) _ hact, (hact _ (hD.rest hP.good)).symm⟩
  | zero => exact ⟨⊥, inferInstance, bot_le, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    obtain ⟨V', h1', h2', h3'⟩ := hy
    exact ⟨V ⊔ V', inferInstance, sup_le h2 h2', fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (h3 k hk) (h3' k hk)⟩
  | smul c x _ hx =>
    obtain ⟨V, h1, h2, h3⟩ := hx
    exact ⟨V, h1, h2, fun k hk => by rw [map_smul]; exact V.smul_mem c (h3 k hk)⟩
