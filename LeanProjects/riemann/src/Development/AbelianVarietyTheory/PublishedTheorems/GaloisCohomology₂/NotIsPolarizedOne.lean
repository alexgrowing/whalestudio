import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp.Model

abbrev Qi : Type := CyclotomicField 4 ℚ

instance cmQi : IsCMField Qi := IsCyclotomicExtension.Rat.isCMField Qi (S := {4}) ⟨4, rfl, by norm_num⟩

theorem hyp_inhabited (l : ℕ) [Fact l.Prime] : Nonempty (Qbar l ≃+* ℂ) ∧
    ∃ (π : CuspSub Qi 1) (χ : HChar (maximalRealSubfield Qi)), (CG.mk π).IsRegAlg ∧ IsPolarized π χ :=
  ⟨GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l, _, _, isPolarized_triv.2, isPolarized_triv.1⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]
  {l : ℕ} [Fact l.Prime]

theorem not_isPolarized_one (π : CuspSub E 1) : ¬ IsPolarized π 1 := fun h => by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
  have h1 : (1 : ℂˣ) = (-1) ^ 1 := h.sign v
  have := congrArg (Units.val) h1
  norm_num at this

theorem HT_char {ξ : HChar E} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin 1) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf ((CuspSub.triv E le_rfl).twist ξ) χ ι r wt HT) (τ : E →+* Qbar l) {n : ℤ}
    (hn : expo ξ (ι.toRingHom.comp τ) = n) : HT τ = {-n} := by
  apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
  rw [H.weights τ]
  change ((CG.ofChar ξ).infChar _).map _ = _
  rw [CG.infChar_ofChar, hn]
  simp

theorem locComp_triv {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin 1) (w.adicCompletion E))}
    (h : (CuspSub.triv E le_rfl).IsLocComp w σ) (hχ) :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.ofChar 1 hχ := by
  obtain ⟨f, h0, hf⟩ := h
  have hact : ∀ g (φ : (CuspSub.triv E (le_refl 1)).V), (CuspSub.triv E le_rfl).locRep w g φ = φ := fun g φ => by
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 φ.2
    refine Subtype.ext ?_
    change act (.fin _) φ.1 = φ.1
    rw [← e]; rfl
  let L : ℂ ≃ₗ[ℂ] (CuspSub.triv E (le_refl 1)).V := LinearEquiv.toSpanNonzeroSingleton ℂ _ (oneFn E 1) oneFn_ne_zero
  let f' : σ.V →ₗ[ℂ] ℂ := L.symm.toLinearMap ∘ₗ f
  have hf' : ∀ g v, f' (σ.ρ g v) = f' v := fun g v => by simp [f', hf, hact]
  have h0' : f' ≠ 0 := fun h => h0 (LinearMap.ext fun v => L.symm.injective (by simpa [f'] using LinearMap.congr_fun h v))
  have hinj : Function.Injective f' := by
    rcases ((isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f') (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢; rw [hf', hv]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0'
  have hsurj : Function.Surjective f' := LinearMap.range_eq_top.1
    ((eq_bot_or_eq_top (LinearMap.range f')).resolve_left fun h => h0' (LinearMap.range_eq_bot.1 h))
  refine (IrrGL.of_eq_of (σ := (SmGL.IrrRep.det (Fin 1) 1 hχ).ρ) (hs' := (SmGL.IrrRep.det (Fin 1) 1 hχ).smooth)
    (hi' := (SmGL.IrrRep.det (Fin 1) 1 hχ).irr)).2 ⟨.mk (LinearEquiv.ofBijective f' ⟨hinj, hsurj⟩) fun g => ?_⟩
  ext v
  exact (hf' g v).trans (one_smul ℂ _).symm

omit [IsCMField E] in

theorem isWDOf_one {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) :
    IsWDOf ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)) := by
  obtain ⟨x, hx⟩ := (exists_isWDOf_iff (h := h) (ι := ι) (r := (1 : G E Ω →* GL (Fin 1) (Qbar l))) hl
    (isTameChar_tameL h hl)).2 ⟨0, (isMonodromy_zero_iff (h := h)).2 (.of_trivial fun _ => rfl)⟩
  have e : wdOf h hl ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) :=
    wdOf_eq_mk hl _ rfl fun g => LinearMap.ext fun v => funext fun i => by simp
  rwa [← e, hx.wdOf_eq hl]

theorem isGalRepOf_triv (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (hpol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ ∧
      μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* _) = 1)
    (habove : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsAttachedAbove (CuspSub.triv E (le_refl 1)) ι 1 (fun _ => {0}) P h Bw hj) :
    IsGalRepOf (CuspSub.triv E (le_refl 1)) χ ι (1 : G E Ω →* GL (Fin 1) (Qbar l)) 0 (fun _ => {0}) where
  cont := continuous_const
  ss W _ := let ⟨W', h⟩ := W.exists_isCompl; ⟨W', fun g v hv => by simpa using hv, h⟩
  pol := by
    obtain ⟨μ, h1, h2⟩ := hpol
    refine ⟨μ, h1, fun c _ => ?_⟩
    rw [h2]
    simpa using isConjDual_one c
  away w hl A h rc hrc σ hσ := by
    rw [rec_algNorm hrc]
    obtain ⟨a, ha, ε, -, H⟩ := hrc
    have h1 : SmGL.IsSmoothChar (1 : (w.adicCompletion E)ˣ →* ℂˣ) := by
      simpa using isSmoothChar_absPow (k := w.adicCompletion E) 0
    rw [locComp_triv hσ h1, H.one]
    have e : ((1 - ((1 : ℕ) : ℝ)) / 2) = 0 := by simp
    rw [e, WD.lpTw_zero]
    convert isWDOf_one hl h ι using 1
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
    ext i; simp [WDRep.ofChars]
  pure w hl A h := ⟨_, isWDOf_one hl h ι, by
    rw [Int.cast_zero, zero_div, WD.lpTw_zero]
    simp [WD.tempered_diag_iff]⟩
  weights τ := by
    rw [← CuspSub.twist_one (CuspSub.triv E (le_refl 1))]
    change _ = ((CG.ofChar 1).infChar _).map _
    rw [CG.infChar_ofChar, CG.expo_one]
    simp
  weights_conj τ := by simp
  above := habove

omit [IsCMField E] in

theorem pure_cyc {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) :
    ((wdOf h hl ι ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l))).lpTw (((-2 : ℤ) : ℝ) / 2)).tempered := by
  rw [wdOf_cyc, WD.lpTw_add, show (1 : ℝ) + ((-2 : ℤ) : ℝ) / 2 = 0 by norm_num, WD.lpTw_zero]
  simp [WD.tempered_diag_iff]

end GlobalTheory.GalOfCusp.Model
