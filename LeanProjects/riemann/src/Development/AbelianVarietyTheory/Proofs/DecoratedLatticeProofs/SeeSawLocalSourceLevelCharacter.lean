import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section
namespace GlobalTheory.SeeSaw.LocSrc

section Local
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLoc_one (p : Place D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    p.IsLoc F 1 1 := by
  refine ⟨fun i j => by simp [Formalism.L2.Theta.mt], ?_⟩
  have : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
  simp [F.βγ]

theorem isComp_inv (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ⁻¹ μ) : p.IsComp χ μ⁻¹ := by
  intro x a ha
  have h1 := h x a ha
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at h1 ⊢
  rw [h1, inv_inv]

theorem valuation_det_of_mem_stabLat {Y : Type} [Fintype Y] [DecidableEq Y] {g h : GL Y k} (hh : h ∈ GlobalTheory.StepData.stabLat g) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  have h1 := valuation_det_of_mem_KO (GlobalTheory.StepData.mem_stabLat.1 hh)
  have e : Matrix.GeneralLinearGroup.det (g⁻¹ * h * g) = Matrix.GeneralLinearGroup.det h := by
    rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [e] at h1

theorem om_Phi {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hu : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) (j a : ℕ) (H : j + a = s) (hb : j + (a + 1) = s + 1)
    (x : ((S.T t).lev j (a + 1) hb).J) :
    GlobalTheory.SplitWeil.om (μ (j + 1)) x.1 1 ((S.T t).Phi j a H) = (((S.T t).lev j (a + 1) hb).lam x : ℂ) • (S.T t).Phi j a H := by
  obtain ⟨e1, e2⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq k s κ S t μ hμ hu
  have hx : x.1 ∈ (((withMu S μ hμ).T t).lev j (a + 1) hb).J := by rw [(e2 j (a + 1) hb).1]; exact x.2
  have L : ((withMu S μ hμ).T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (L.1 j a H).1 ⟨x.1, hx⟩
  rw [e1, (e2 j (a + 1) hb).2 x.1 hx x.2] at h1
  exact h1

end Local

theorem seeSaw_local_sourceLevel_character : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ (j : ℕ) (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (μ : ℕ → G.kˣ →* ℂˣ), (∀ i, IsTame (μ i)) → (∀ i (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ i x = G.S.μ i x) → (ofSplit G.q).IsComp χS⁻¹ (μ (j + 1)) → (∃ μ', (ofSplit G.q).IsComp χT μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) → j ≤ G.s → ∀ (b : ℕ) (hb : j + b = G.s + 1) (x : ((G.S.T (Fin D.R.t)).lev j b hb).J) (h : GA D (c.V j)), (ofSplit G.q).IsLoc (G.FY j b hb) h x.1 → ∀ f : WO (c.V j) (c.V (j + 1)) → ℂ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f → om (h, 1) (comb c.ψ _ _ (G.eg j) f) = (((G.S.T (Fin D.R.t)).lev j b hb).lam x : ℂ) • comb c.ψ _ _ (G.eg j) f := by
  intro D c v G hc hv j χS χT ω hω μ hμ hu hS hT hj b hb x h hl f hf
  obtain ⟨μ', hT, hT'⟩ := hT
  obtain ⟨a, rfl⟩ : ∃ a, b = a + 1 := ⟨b - 1, by omega⟩
  have H : j + a = G.s := by omega
  have H' : j + 1 + a = G.s + 1 := by omega
  have hm := G.hs
  obtain ⟨Tm, hTm, hO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ (c.V j) (c.V (j + 1)) (G.FY j (a + 1) hb) (G.FY (j + 1) a H')
    c.ψ G.S.ψ hc.std G.char G.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (G.latY j (a + 1) hb) (G.latY (j + 1) a H')).2 f hf
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k) (Y := XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a)
    (Y' := XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1))
  have R : (G.S.T (Fin D.R.t)).Regular := Chain.ofType_regular _ _ _ _ _
  let Φ : SB (Matrix (XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (a + 1)) G.k) :=
    ⟨(G.S.T (Fin D.R.t)).Phi j a H, R.1 j a H⟩
  have e1 : Tm Φ = comb c.ψ _ _ (G.eg j) f := by
    rw [← hO O hO1]
    exact (G.eg_is j a H).2 Tm hTm O Φ hO1 rfl
  have hd := valuation_det_of_mem_stabLat ((R.2.2 j (a + 1) hb).2.2 x.2)
  have e2 : ((μ (j + 1))⁻¹ * μ'⁻¹) (Matrix.GeneralLinearGroup.det x.1) = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, ← mul_inv, mul_comm, hT' _ hd, inv_one]
  have key := GlobalTheory.T.weilDatum_localModel_formula D G.k (ofSplit G.q) c.ψ _ _ χS χT ω hω (μ (j + 1))⁻¹ μ' (isComp_inv _ hS) hT _ _
    (G.FY j (a + 1) hb) (G.FY (j + 1) a H') Tm hTm h x.1 1 1 hl (isLoc_one _ _) Φ
    ((((G.S.T (Fin D.R.t)).lev j (a + 1) hb).lam x : ℂ) • Φ) (by
      rw [e2, inv_inv, Units.val_one, one_smul]
      exact (om_Phi G.S (Fin D.R.t) μ hμ hu j a H hb x).symm)
  rw [← e1, key, map_smul]

end GlobalTheory.SeeSaw.LocSrc
end
