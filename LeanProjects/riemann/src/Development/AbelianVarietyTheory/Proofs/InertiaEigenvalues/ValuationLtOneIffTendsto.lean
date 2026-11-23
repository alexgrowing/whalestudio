import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec.TwistInert

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem valuation_lt_one_iff_tendsto (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h1 : 1 ≤ valuation K x := not_lt.1 hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ h1
  exact absurd hn (not_lt.2 h2)

theorem valuation_lt_one_map (f : K →+* L) (hf : Continuous f) {x : K} (hx : valuation K x < 1) :
    valuation L (f x) < 1 := by
  rw [valuation_lt_one_iff_tendsto] at hx ⊢
  simpa [Function.comp_def, map_pow] using (hf.tendsto 0).comp hx

theorem valuation_eq_one_of_map (f : K ≃+* L) (hf : Continuous f) {x : K}
    (hx : valuation L (f x) = 1) : valuation K x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hv : 0 < valuation K x := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hx0
  rcases lt_trichotomy (valuation K x) 1 with h | h | h
  · exact absurd hx (ne_of_lt (valuation_lt_one_map f.toRingHom hf h))
  · exact h
  · have h1 : valuation K x⁻¹ < 1 := by rw [map_inv₀]; exact (inv_lt_one₀ hv).2 h
    have h2 := valuation_lt_one_map f.toRingHom hf h1
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀, hx, inv_one] at h2
    exact absurd h2 (lt_irrefl 1)

end Val

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (χ : G →* ℂˣ) :
    (twist π χ).Equiv (twist σ χ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    have e := LinearMap.congr_fun (φ.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, twist_apply, map_smul]
    congr 1

def push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) :
    ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ :=
  μ.comp (Units.map (I.i k v).symm.toRingHom.toMonoidHom)

theorem isUnram_push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {μ : ℚ_[D.host.g k]ˣ →* ℂˣ}
    (hμ : IsUnram μ) : IsUnram (push I k v μ) := by
  intro y hy
  apply hμ
  apply valuation_eq_one_of_map (I.i k v) (I.cont k v)
  simpa using hy

theorem detChar_push {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (μ : ℚ_[D.host.g k]ˣ →* ℂˣ)
    (g : GL (Fin n) ℚ_[D.host.g k]) :
    detChar (Fin n) (push I k v μ) (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = detChar (Fin n) μ g := by
  rw [detChar_apply, detChar_apply, push, MonoidHom.comp_apply]
  congr 1
  ext
  have e : ((g : Matrix (Fin n) (Fin n) ℚ_[D.host.g k]).map (I.i k v)).det = I.i k v (g : Matrix (Fin n) (Fin n) ℚ_[D.host.g k]).det :=
    ((I.i k v).toRingHom.map_det _).symm
  simp [e]

def twistPullEquiv {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) (μ : ℚ_[D.host.g k]ˣ →* ℂˣ)
    (hμ : IsSmoothChar (push I k v μ)) :
    (twist (pull I k v σ).ρ (detChar (Fin n) μ)).Equiv
      (pull I k v (irrTwist σ (detChar (Fin n) (push I k v μ)) hμ.detChar)).ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => LinearMap.ext fun x => by
    show (detChar (Fin n) μ g : ℂ) • σ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) x =
      (detChar (Fin n) (push I k v μ) (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) : ℂ) •
        σ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) x
    rw [detChar_push]

theorem inePol_lpTwist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (y : GlobalTheory.WeilDeligne.WD h) (ξ : GlobalTheory.WeilDeligne.Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ)
    {σ : G E Ω} (hσ : σ ∈ Ine A) (h1 : ξ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) = 1) :
    (y.lpTwist ξ hξ).inePol σ = y.inePol σ := by
  rw [GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ, GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ hσ]
  obtain ⟨m, b, rfl⟩ := y.exists_rep
  rw [GlobalTheory.WeilDeligne.WD.lpTwist_mk, GlobalTheory.WeilDeligne.WD.charPol_mk, GlobalTheory.WeilDeligne.WD.charPol_mk]
  congr 1
  show ((ξ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) : ℂˣ) : ℂ) • b.ρ (GlobalTheory.WeilDeligne.ineIncl h ⟨σ, hσ⟩) = _
  rw [h1, Units.val_one, one_smul]

theorem inePol_inert : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ (k : Fin 2) (v : D.nd.PlG k) (ρ : Supp.GLRep (D.host.g k)) (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible) (x : GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k]), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x → D.naut.inePol (rc k v ρ.1 ρ.2) (D.ntypes.tg k v) = D.naut.inePol (rc k v x.1 (Rep.of x.rep)) (D.ntypes.tg k v) := by
  intro hL D T I rc hrc k v ρ hs hi x hx
  obtain ⟨μ, hμ, rfl⟩ := hx
  obtain ⟨σ₁, ⟨e₁⟩⟩ := GlobalTheory.TypeRec.Model.exists_pull I k v ρ.2 ⟨(GlobalTheory.GLp.Model.isIrrRep_iff _).2 hi, hs⟩
  have hμ' : IsUnram (push I k v μ) := isUnram_push I k v hμ
  have hμs : IsSmoothChar (push I k v μ) := isSmoothChar_of_isUnram hμ'
  have e₂ : Nonempty (Rep.of ((IrrGL.of ρ.2.ρ hs hi).tw μ (isSmoothChar_of_isUnram hμ)).rep ≅
      pull I k v (irrTwist σ₁ (detChar (Fin ρ.1) (push I k v μ)) hμs.detChar)) :=
    ⟨Rep.mkIso ((IrrGL.twEquiv _ _ _).symm.trans ((twistEquiv (IrrGL.equivOf ρ.2.ρ hs hi).symm _).trans
      ((twistEquiv (Representation.equivOfIso e₁) _).trans (twistPullEquiv I k v σ₁ μ hμs))))⟩
  have h1 := hrc k v _ σ₁ ρ.2 ⟨e₁⟩
  have h2 := hrc k v _ _ _ e₂
  have hc : GlobalTheory.LocLanglands.cls (irrTwist σ₁ (detChar (Fin ρ.1) (push I k v μ)) hμs.detChar) =
      (GlobalTheory.LocLanglands.cls σ₁).tw (push I k v μ) hμs :=
    congrArg (Sigma.mk _) (clTwist_cl _ _ _).symm
  obtain ⟨a, ha, ε, -, H⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), T.inePol _ _ _ (D.ntypes.tg_mem k v), h1, h2]
  have h3 := congrArg (fun z => (GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) z).inePol (D.ntypes.tg k v)) hc
  have h4 := congrArg (fun z => GlobalTheory.WeilDeligne.WD.inePol z (D.ntypes.tg k v)) (H.tw_eq (GlobalTheory.LocLanglands.cls σ₁) _ hμs)
  refine Eq.trans ?_ (h3.trans h4).symm
  exact (inePol_lpTwist _ _ _ (D.ntypes.tg_mem k v)
    (hμ' _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp)))).symm

end GlobalTheory.TypeRec.TwistInert
