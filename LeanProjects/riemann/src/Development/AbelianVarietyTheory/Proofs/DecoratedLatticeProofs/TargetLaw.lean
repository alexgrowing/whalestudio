import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

namespace GlobalTheory.SeeSaw.LocTarget

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {Y : Type} [Fintype Y] [DecidableEq Y] {S : HSp D} (F : GlobalTheory.LocMod.Frame k S.rank Y) : p.IsLoc F 1 1 := by
  have h1 : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨fun i j => by rw [h1, sub_self, Matrix.zero_apply, mul_zero], ?_⟩
  rw [h1, Units.val_one, Matrix.mul_one, F.βγ]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isComp_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, h x a ha, MonoidHom.inv_apply, Circle.coe_inv, inv_inv]

theorem om_phi {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j b : ℕ) (H : j + b = s) (hb : j + 1 + b = s + 1)
    (x : ((S.T t).lev (j + 1) b hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) 1 x.1 ((S.T t).Phi j b H) =
      ((((S.T t).lev (j + 1) b hb).lam x : ℂ))⁻¹ • (S.T t).Phi j b H := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hL : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  obtain ⟨hJ, hl⟩ := h2 (j + 1) b hb
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev (j + 1) b hb).J := by rw [hJ]; exact x.2
  have := (hL.1 j b H).2 ⟨x.1, hx⟩
  rw [h1, hl x.1 hx x.2, Units.val_inv_eq_inv_val] at this
  exact this

theorem target_law : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → ∀ (b : ℕ) (hb : j + 1 + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev (j + 1) b hb).J) (h : GA D (c.V (j + 1))), (ofSplit G.q).IsLoc (G.FY (j + 1) b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (1, h) (comb c.ψ _ _ (G.eg j) f) = ((((G.S.T (Fin D.R.t)).lev (j + 1) b hb).lam x : ℂ))⁻¹ • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT b hb x h hx f hf
  have hs := G.hs
  have H : j + b = G.s := by omega
  obtain ⟨μT, hT, -⟩ := hT
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY j (b + 1) (by omega)) (G.FY (j + 1) b hb) c.ψ G.S.ψ
    hc.std G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (b + 1) (by omega)) (G.latY (j + 1) b hb)).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin b)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (b + 1))
  have hR : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  have e1 := (G.eg_is j b H).2 Tm hTm O ⟨_, hR.1 j b H⟩ hO1 rfl
  rw [← hO O hO1, ← e1, ← map_smul]
  refine GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω _ μT (isComp_inv _ hS) hT _ _ _ _ Tm hTm 1 1 h x.1
    (isLoc_one _ _) hx _ _ ?_
  rw [map_one, map_one, Units.val_one, one_smul, inv_inv]
  exact (om_phi G.S _ μ hμ hu j b H hb x).symm

end GlobalTheory.SeeSaw.LocTarget
