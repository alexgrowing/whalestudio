import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem of_model (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {R r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hc : Continuous R) (hs : IsSSRep R) (H : ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ)
    (hr : Continuous r) (ha : AttC ι r π) (w) (σ) (hσ : π.IsLocComp w σ) : LocGlob ι r w σ := by
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => (H w σ hσ A h rc hrc).1 hw, hf⟩
  intro A h rc hrc
  obtain ⟨h1, h2⟩ := H w σ hσ A h rc hrc
  refine ⟨fun hw => (h1 hw).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], fun O _ _ _ Bw hj => ?_⟩
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) (h2 O Bw hj).1
  exact ⟨h3.1, by rw [h3.2]; exact (h2 O Bw hj).2⟩

private theorem cls_char {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E)
    {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (h : ((CuspSub.triv E le_rfl).twist χ).IsLocComp w σ) (hχ) :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar (χ.loc w) hχ := by
  obtain ⟨f, h0, hf⟩ := h
  have hop : ∀ g (x : ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V),
      ((CuspSub.triv E le_rfl).twist χ).locRep w g x = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • x := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.op_triv_twist, ← CuspSub.chiDet_locGL]
    simp [opMul, opTriv, opAdd]
  let L : ℂ ≃ₗ[ℂ] ((CuspSub.triv E le_rfl).twist χ : CuspSub E 1).V :=
    (LinearEquiv.toSpanNonzeroSingleton ℂ _ (oneFn E 1) oneFn_ne_zero).trans ((CuspSub.triv E le_rfl).toTwist χ)
  let f' : σ.V →ₗ[ℂ] ℂ := L.symm.toLinearMap ∘ₗ f
  have hf' : ∀ g v, f' (σ.ρ g v) = ((CuspSub.locDet 1 χ w g : ℂˣ) : ℂ) • f' v := fun g v => by simp [f', hf, hop]
  have h0' : f' ≠ 0 := fun h => h0 (LinearMap.ext fun v => L.symm.injective (by simpa [f'] using LinearMap.congr_fun h v))
  have hinj : Function.Injective f' := by
    rcases ((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f') (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢; rw [hf', hv, smul_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0'
  have hsurj : Function.Surjective f' := LinearMap.range_eq_top.1
    ((eq_bot_or_eq_top (LinearMap.range f')).resolve_left fun h => h0' (LinearMap.range_eq_bot.1 h))
  refine (IrrGL.of_eq_of (σ := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).ρ) (hs' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).smooth)
    (hi' := (GlobalTheory.SmGL.IrrRep.det (Fin 1) _ hχ).irr)).2 ⟨.mk (LinearEquiv.ofBijective f' ⟨hinj, hsurj⟩) fun g => ?_⟩
  ext v
  exact hf' g v

private theorem rank_one (P : Hypotheses₂) {K Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {π : CuspSub K 1} (hreg : (CG.mk π).IsRegAlg) :
    ∃ R : G K Ω →* GL (Fin 1) (Qbar l), Continuous R ∧ IsSSRep R ∧ ∀ w σ, π.IsLocComp w σ → LocGlob ι R w σ := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  choose m hm using (CG.isRegAlg_ofChar χ).1 hreg
  have hχ := GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo K χ m hm
  obtain ⟨art, hart, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμ, hL⟩, -⟩ := hμ l ι χ m hχ
  have hval : ∀ g, (GlobalTheory.TripleGal.rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) = Matrix.scalar (Fin 1) (μ g : Qbar l) :=
    fun g => rfl
  have hc : Continuous (GlobalTheory.TripleGal.rk1 μ) := by
    refine (Continuous.units_map _ ?_).comp hμ
    exact continuous_matrix fun i j => by
      fin_cases i; fin_cases j
      simpa using continuous_id'
  refine ⟨_, hc, fun W _ => ?_, fun w σ hσ A h rc hrc => ?_⟩
  · obtain ⟨W', hW⟩ := W.exists_isCompl
    refine ⟨W', fun g v hv => ?_, hW⟩
    have := W'.smul_mem (μ g : Qbar l) hv
    convert this using 1
    ext i
    simp [hval, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hcp := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have e0 : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
  rw [rec_algNorm hrc, e0, WD.lpTw_zero, cls_char χ hσ hcp.1]
  obtain ⟨a, ha, ε, -, HL⟩ := hrc
  rw [HL.one _ hcp.1]
  refine ⟨fun hw => ?_, fun O _ _ _ Bw hj => ⟨?_, ?_⟩⟩
  · have h1 := isWDOf_wdOf (h := h) (r := GlobalTheory.TripleGal.rk1 μ) hw ι (Units.continuous_val.comp hc)
    rwa [wdOf_eq_mk hw (WDRep.ofChars h (fun _ : Fin 1 => (χ.loc w).comp a) fun _ => ha.smooth hcp.1) rfl fun g => by
      refine LinearMap.ext fun v => funext fun i => ?_
      rw [Subsingleton.elim i 0]
      simp [toEndC_apply, Matrix.mulVec, dotProduct, hval, hL.loc_away (Or.inl hw) _ _ (ha.glob art hart g)]] at h1
  · obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val))
      (GlobalTheory.Published.heckeLAdicCharacterAbove_iff.1 P.litN.aut.chA K Ω l _ _ ⟨T⟩ ι art hart χ m μ hχ hμ hL w A h O Bw hj).1
  · exact Lev.SsCmp.of_eq (P.litN.aut.chW K Ω l _ _ (Loc.tiedP l) ι art hart χ m μ hχ hμ hL w A h O Bw hj _ hcp a ha)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.compatCsd :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CompatCsd := by
  intro PH F Ω _ _ _ _ _ _ l _ ι n hn r π hr hreg hd ha
  have P := PH.toClassicalTheorems
  rcases hn.eq_or_lt with rfl | hn
  · obtain ⟨R, hc, hs, H⟩ := rank_one (Ω := Ω) P ι hreg
    exact of_model P hc hs H hr ha
  · obtain ⟨R, hc, hs, Haw, Hab⟩ := P.ss F Ω l ι n hn π hd (P.litN.aut.coh F n (by omega) π hreg)
    refine of_model P hc hs (fun w σ hσ A h rc hrc => ⟨fun hw => Haw w hw A h rc hrc σ hσ, fun O _ _ _ Bw hj => ?_⟩) hr ha
    have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
    exact ⟨h1.1, h1.2 σ hσ rc hrc⟩

end
