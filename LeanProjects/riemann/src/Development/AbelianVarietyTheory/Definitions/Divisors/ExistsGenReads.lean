import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.CcModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realM_mt {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hth : IsInfEmb τ th) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W th h := by
  have e : θ hτ.choose = th :=
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ _ _ (by have := hθ hτ.choose; rwa [← hτ.choose_spec] at this) hth
  rw [realM, dif_pos hτ, compAt, e]
  rfl

theorem exists_atComp {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hΨ : ∀ k, ∀ τ ∈ (U.X k).Ψ, ∃ ρ, τ = tauE D ρ)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hD : DictLat U W hr dict ι e F ik φ th x₀) (h : GA D W) :
    ∃ γ, AtComp θ W hr U.X dict x₀ h γ := by
  obtain ⟨γ, hγ, h1, -, h3⟩ := hD.2 h
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [h1, latR, Submodule.map_coe]
    rfl
  · funext τ
    have := h3 τ
    rw [← realM_mt hθ W (γ * h) τ.1 (hΨ _ _ τ.2) _ (hth _ τ)] at this
    exact this

theorem exists_genReads {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (k : U.Comp) (x : (U.X k).dom) (hx : IsUnitFr (U.X k) x.1) :
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
      (ϑ : (Fin g → ℂ) → ℂ), IsSympl (U.X k) bas ∧ IdxIs c σ (U.X k) idx e ∧ GenReads U k bas idx e x ϑ ∧
        MeanOne (U.X k) bas idx x.1 (U.X k).Λ ϑ := by
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ _ hσ hU' h1 Wt k
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 0 := ⟨fun _ => antitone_const, by simp⟩
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ _ Wt.g 0 (U.X k) (fun _ => 0) Wt.e hσ hU.1
    (hU.2.1 k).1 (hU.2.1 k).2 huw.2.1 hdom
  have hper : ∀ x v j, pv (U.X k) Dc.idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (Formalism.L2.PjFree.relab c σ (Wt.e j).1) (Wt.e j).2 := fun x v j => by
    rw [Dc.per_eq, hDe]
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = Formalism.L2.PjFree.relab c σ (Wt.e j).1 := fun j => by
    rw [Dc.ty_eq, hDe]
  obtain ⟨A, -, ϑ, hA, hm⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ _ hσ hU' h1 Wt k Dc.bas Dc.idx Dc.sympl hper hty x hx
  exact ⟨Wt.g, Dc.bas, Dc.idx, Wt.e, ϑ, Dc.sympl, ⟨hper, hty⟩, ⟨A, hA⟩, hm⟩

variable {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc cc' : U.Comp → ℂ}

theorem ccIs_smul (h : CcIs θ V W hr U dict mu x₀ om f₀ cc) (a : ℂ) (ha : ‖a‖ = 1) :
    CcIs θ V W hr U dict mu x₀ om (a • f₀) (fun k => a * cc k) := by
  refine ⟨fun k => by rw [norm_mul, ha, h.1 k, mul_one], fun g γ hg hx' n bas idx e hs hi ϑ hϑ w hw => ?_⟩
  rw [map_smul, Pi.smul_apply, h.2 g γ hg hx' n bas idx e hs hi ϑ hϑ w hw, smul_eq_mul]
  ring

theorem ccIs_unique (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (h : CcIs θ V W hr U dict mu x₀ om f₀ cc)
    (h' : CcIs θ V W hr U dict mu x₀ om f₀ cc') (g γ : GA D W) (hg : AtComp θ W hr U.X dict x₀ g γ)
    (hd : (dict g).2 ∈ (U.X (dict g).1).dom) (hu : IsUnitFr (U.X (dict g).1) (dict g).2) (w : WO V W)
    (hw : w.map (finPart D) = 0) (hne : om (1, γ * g) f₀ w ≠ 0) : cc (dict g).1 = cc' (dict g).1 := by
  obtain ⟨n, bas, idx, e, ϑ, hs, hi, hϑ, -⟩ := exists_genReads U hσ hU h1 (dict g).1 ⟨_, hd⟩ hu
  have e1 := h.2 g γ hg hd n bas idx e hs hi ϑ hϑ w hw
  have e2 := h'.2 g γ hg hd n bas idx e hs hi ϑ hϑ w hw
  rw [mul_assoc, mul_assoc] at e1 e2
  have hB := right_ne_zero_of_mul (e1 ▸ hne)
  exact mul_right_cancel₀ hB (e1.symm.trans e2)

end

end GlobalTheory.AdTh.CcModel
