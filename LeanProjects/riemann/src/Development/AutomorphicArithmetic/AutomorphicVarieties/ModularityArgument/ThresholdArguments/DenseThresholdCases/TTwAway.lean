import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.TwAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem det_rank_one_rep {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) :
    Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
  ext g
  simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
private theorem tw_eq {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l)) (μ : Γ →* (Qbar l)ˣ) :
    Af.tw R μ = Formalism.MainNotions.SumRepresentations.At.twGL R (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
  rw [det_rank_one_rep]
  ext g i j
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
theorem UpperTheory.V.Z.Desc.W.twist_away_statement : _root_.UpperTheory.V.Z.Desc.W.TwAwayAlt := by
  intro P K Ω _ _ _ _ _ _ l _ ι n R hR art κ m μ hart hμ hL w hw τ τ' hG he A h rc hrc h1
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  obtain ⟨a, ha, ε, HL⟩ := toV' hrc
  have e : rc (algNorm τ') = (rc (algNorm τ)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [algNorm, algNorm, HL.nu_eq, HL.nu_eq, GlobalTheory.NuShift.lpChar_lpTw, ← HL.twist _ _ _ hG, GlobalTheory.LocGL.IrrGL.tw_of]
    exact congrArg (fun x => (rc x).lpTw _) (IrrGL.of_eq_of.2 he)
  rw [e, HL.one _ hc.1]
  have hcR := Units.continuous_val.comp hR
  have hct : Continuous fun g => ((Af.tw R μ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    simp only [Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul hcR
  have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
    fun g => rfl
  have h3 := isWDOf_wdOf (h := h) (r := Af.tw R μ) hw ι hct
  have h4 := wdOf_twGL_det K Ω A w h l hw ι n R _ hcR (continuous_rank_one_rep hμ)
  rw [← tw_eq, h1.wdOf_eq hw,
    wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (κ.loc w).comp a) fun _ => ha.smooth hc.1) rfl fun g => by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [Subsingleton.elim i 0]
    simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h4
  rw [h4] at h3
  exact h3
end
