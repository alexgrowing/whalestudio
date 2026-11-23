import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Untwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
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

private theorem tw_comp {Γ Γ' : Type} [Group Γ] [Group Γ'] {l : ℕ} [Fact l.Prime] {n : ℕ} (R : Γ →* GL (Fin n) (Qbar l))
    (μ : Γ →* (Qbar l)ˣ) (f : Γ' →* Γ) :
    (Af.tw R μ).comp f = Formalism.MainNotions.SumRepresentations.At.twGL (R.comp f) (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp f)) := by
  rw [tw_eq]; rfl

private theorem continuous_rank_one_rep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] {μ : Γ →* (Qbar l)ˣ}
    (hμ : Continuous μ) :
    Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i; fin_cases j
  have := Units.continuous_val.comp hμ
  simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this

theorem UpperTheory.galois_character_of_algebraic_hecke :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (K Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : G K Ω →* GL (Fin n) (Qbar l)), Continuous R → (∃ HT, Af.HasHT R HT) → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsAlgPos κ m → Continuous μ → IsLAdicOf art ι κ m μ → (∃ HT, Af.HasHT (Af.tw R μ) HT) ∧ ∀ (w : Plc K) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))), Af.LocGlob ι R w τ → Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Af.LocGlob ι (Af.tw R μ) w τ' := by
  intro P K Ω _ _ _ _ _ _ l _ ι n R hR hHT art κ m μ hart hκ hμ hL
  obtain ⟨HT, hHT⟩ := hHT
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have H1 : Af.HasHT (Af.tw R μ) fun τ => (HT τ).map (· + -m (ι.toRingHom.comp τ)) := by
    intro w A h O _ _ _ Bw hj
    obtain ⟨d1, j1⟩ := hHT w A h O Bw hj
    obtain ⟨d2, -, -, j2⟩ :=
      GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj
    have t := GlobalTheory.TwistAbove.twist_above l _ _ ⟨T⟩ K Ω _ O Bw n (R.comp (Dec (F := K) A).subtype)
      ((Af.tw R μ).comp (Dec (F := K) A).subtype) (μ.comp (Dec (F := K) A).subtype) fun g => Af.tw_val R μ g.1
    exact ⟨t.1 d1 d2, fun τ L' τ' hτ => t.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ)⟩
  refine ⟨⟨_, H1⟩, fun w τ τ' hτ he A h rc hrc => ?_⟩
  obtain ⟨h1, h2⟩ := hτ A h rc hrc
  have hc := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) κ
  have e : rc (algNorm τ') = (rc (algNorm τ)).lpChar (rc (.ofChar (κ.loc w) hc.1)) := by
    rw [rec_algNorm hrc, rec_algNorm hrc, GlobalTheory.NuShift.lpChar_lpTw]
    obtain ⟨a, ha, ε, -, HL⟩ := hrc
    rw [← HL.twist, GlobalTheory.LocGL.IrrGL.tw_of]
    exact congrArg (fun x => (rc x).lpTw _) (IrrGL.of_eq_of.2 he)
  rw [e]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hc.1]
  have hcR := Units.continuous_val.comp hR
  have hct : Continuous fun g => ((Af.tw R μ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    simp only [Af.tw_val]
    exact (Units.continuous_val.comp hμ).smul hcR
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩
  · have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
      fun g => rfl
    have h3 := isWDOf_wdOf (h := h) (r := Af.tw R μ) hw ι hct
    have h4 := wdOf_twGL_det K Ω A w h l hw ι n R _ hcR (continuous_rank_one_rep hμ)
    rw [← tw_eq, (h1 hw).wdOf_eq hw,
      wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (κ.loc w).comp a) fun _ => ha.smooth hc.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h4
    rw [h4] at h3
    exact h3
  · obtain ⟨p1, w1⟩ := h2 O Bw hj
    have p3 := P.aut.berger.isPstAt T Bw _ (hct.comp continuous_subtype_val) (H1 w A h O Bw hj).1
    have c2 := (continuous_rank_one_rep hμ).comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := K) A))
    have p2 := P.aut.berger.isPstAt T Bw ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype) c2
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.aut.chA K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj).1
    refine ⟨p3, ?_⟩
    have htw : (Af.tw R μ).comp (Dec (F := K) A).subtype =
        Formalism.MainNotions.SumRepresentations.At.twGL (R.comp (Dec (F := K) A).subtype)
          (Matrix.GeneralLinearGroup.det.comp ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := K) A).subtype)) := by
      exact tw_comp R μ _
    rw [htw] at p3 ⊢
    rw [GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l _ _ ⟨T⟩ ι K Ω A w h O Bw hj n _ _ (hcR.comp continuous_subtype_val) c2 p1 p2 p3,
      P.aut.chW K Ω l _ _ ⟨T⟩ ι art hart κ m μ hκ hμ hL w A h O Bw hj _ hc a ha]
    refine ((UpperTheory.V.Lev.ssCalc K Ω A w h).2.2 _ _ _ ?_).2 w1
    rw [← HL.one _ hc.1]
    exact HL.dim _
