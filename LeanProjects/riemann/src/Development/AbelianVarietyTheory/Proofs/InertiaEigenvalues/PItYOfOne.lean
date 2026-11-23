import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfIndexEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerieStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.ItAllTuples

variable {D : D7}

theorem isItW_smul {V W : HSp D} {S S' : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {M' : DSModel W S'}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω pt It) {c : ℂ} (hc : c ≠ 0) :
    IsItW θ M M' ω pt (c • It) where
  ne := smul_ne_zero hc h.ne
  bdd := by
    intro φ w
    obtain ⟨b, hb⟩ := h.bdd φ w
    refine ⟨‖c‖ * b, fun v => ?_⟩
    have e : ellT M w (inclT M ((c • It) φ (PiTensorProduct.tprod ℂ v))) =
        c * ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v))) := by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul]
    rw [e, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg _)
  eqK := by
    intro τ g hg φ φ' hφ v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
      map_smul, h.eqK τ g hg φ φ' hφ v]
  eqg := by
    intro τ X hX φ φ' hφ v w
    have := (h.eqg τ X hX φ φ' hφ v w).const_mul c
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact this
  invK := by
    intro τ g hg φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      h.invK τ g hg φ φ' v v' hφ hv]
  invg := by
    intro τ X hX φ φ' v v' hφ hv
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ← smul_add,
      h.invg τ X hX φ φ' v v' hφ hv, smul_zero]

theorem pItY_of_one : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, GlobalTheory.Chain.ChainPar D k) → R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → ∀ (k : ℕ), k + 1 < D.R.m → ∀ (t₀ : T) (y : PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (R.MY (k + 1)) →ₗ[ℂ] SmT (R.MY k)), IsItW R.θ (R.MY k) (R.MY (k + 1)) (R.ωY t₀ k) (R.ptY t₀ k) y → R.PItY k y := by
  intro h1 h2 D G _ _ Pl0 T A Ks _ _ _ R hC hL hM hωY hωX hvY hvX k hk t₀ y hy
  have hk0 : k < D.R.m := by omega
  have hSt := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hM.inf hωY hωX hvY hvX
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep h1 h2 D) hC hM.inf hSt k hk
  have hS := hSt.1 t₀ ⟨k, hk0⟩ hk
  have key : ∀ (V W : HSp D) (a b : ℕ) (_ : a = k) (_ : b = k + 1) (M : DSModel V (parB (Ptw D) a))
      (M' : DSModel W (parB (Ptw D) b)) ω f, GlobalTheory.Chain.IsStepWeil ⟨k, hk0⟩ R.ψ V W ω → GlobalTheory.Chain.IsVacVec R.ψ R.θ M M' f →
      ∀ It It' : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It →
        IsItW R.θ M M' ω (GlobalTheory.Chain.ptOf R.ψ R.θ M M' f) It' → ∃ c : ℂ, It' = c • It := by
    intro V W a b ha hb M M' ω f
    subst ha hb
    exact GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries h1 h2 D ⟨a, hk0⟩ V W M M' R.θ R.ψ hM.inf (hC _) ω f
  obtain ⟨c, hc⟩ := key _ _ _ _ (min_eq_left hk0.le) (min_eq_left hk.le) (R.MY k) (R.MY (k + 1)) _ _ hS.1 hS.2 y₀ y
    (hy₀ t₀) hy
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hy.ne (by rw [hc, zero_smul])
  intro t
  rw [hc]
  exact isItW_smul (hy₀ t) hc0

end GlobalTheory.Chain.ItAllTuples

end
