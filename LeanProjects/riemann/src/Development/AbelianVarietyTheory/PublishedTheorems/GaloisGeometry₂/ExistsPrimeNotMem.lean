import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoldsFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDTest

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [NumberField E] [IsAlgClosure E Ω] in

theorem exists_prime_notMem (w : HeightOneSpectrum (𝓞 E)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  by_cases h2 : ((2 : ℕ) : 𝓞 E) ∈ w.asIdeal
  · refine ⟨3, Nat.prime_three, fun h3 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
    have := w.asIdeal.sub_mem h3 h2
    norm_num at this
    exact this
  · exact ⟨2, Nat.prime_two, h2⟩

theorem comp_eq {art : Ideles E →* Gab E Ω} (hart : IsGlobalArtin art) {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    (hn : IsAlgPos χ n) {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a a' : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') :
    ξ.comp a = ξ.comp a' := by
  obtain rfl := eq_loc hξ
  obtain ⟨p, hp, hw⟩ := exists_prime_notMem w
  have := Fact.mk hp
  obtain ⟨ι⟩ : Nonempty (Qbar p ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  obtain ⟨r, -, hr⟩ := hart.exists_isLAdicOf ι hn
  ext σ
  have h1 := hr.loc_away (Or.inl hw) _ _ (ha.glob art hart σ)
  have h2 := hr.loc_away (Or.inl hw) _ _ (ha'.glob art hart σ)
  exact ι.symm.injective (h1.symm.trans h2)

theorem of_parameter (hL : LocalLanglandsGL) (H : HeckeLAdicParameterAbove) : AlgebraicCharacterWD := by
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hn hμ hLa w A h O _ _ _ Bw hj ξ hξ a ha
  obtain ⟨rc, hrc⟩ := (hL.1 E Ω A w h).exists
  obtain ⟨a', ha', hs, e⟩ := rhs_eq h hξ hrc
  rw [H E Ω l P AI hT ι art hart χ n μ hn hμ hLa w A h O Bw hj ξ hξ rc hrc, e]
  obtain rfl := eq_loc hξ
  congr 1
  exact comp_eq hart hn hξ ha' ha

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (ι : Om l ≃+* ℂ)
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw)

theorem lpOfChar_inj {ξ ξ' : Weil h →* ℂˣ} {hξ hξ'} (e : WD.lpOfChar h ξ hξ = WD.lpOfChar h ξ' hξ') : ξ = ξ' := by
  ext σ
  have := congrArg (fun x => WD.eig x σ) e
  simpa only [eig_lpOfChar, Multiset.singleton_inj] using this

theorem isPstAt_of_eq {r : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)} {ξ : (w.adicCompletion E)ˣ →* ℂˣ}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {hs} (hξ : ξ ≠ 1)
    (e : wdAt P ι Bw h hj r = WD.lpOfChar h (ξ.comp a) hs) : IsPstAt P Bw r := by
  by_contra hr
  rw [wdAt_of_not_isPstAt ι Bw h hj hr] at e
  refine hξ (MonoidHom.ext fun x => ?_)
  obtain ⟨σ, rfl⟩ := ha.surj x
  have h1 := congrArg (fun x => WD.eig x σ) e
  simp only [eig_lpOfChar, trivWD] at h1
  have h2 : (WDRep.diag h fun _ : Fin 1 => (1 : ℂˣ)).ρ σ = 1 := by
    ext; simp [WDRep.diag]
  rw [WD.eig_mk, h2] at h1
  have h3 : ((ξ.comp a σ : ℂˣ) : ℂ) ∈ (LinearMap.charpoly (1 : End ℂ (Fin 1 → ℂ))).roots := by
    rw [h1]; simp
  rw [mem_roots (LinearMap.charpoly_monic _).ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly] at h3
  obtain ⟨u, hu⟩ := h3.exists_hasEigenvector
  have h4 := hu.apply_eq_smul
  rw [End.one_apply] at h4
  have h5 : ((ξ.comp a σ : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ hu.2 (h4.symm.trans (one_smul _ _).symm)
  exact Units.ext h5

theorem holds_abs' (hB : DeRhamPotSemistable) (hT : Nonempty (LocTied l P AI))
    {art : Ideles E →* Gab E Ω} (hart : IsGlobalArtin art)
    {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ)
    (hL : IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ)
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) = WD.lpOfChar h (ξ.comp a) (ha.smooth hξ.1) := by
  obtain ⟨T⟩ := hT
  refine CharWDModel.holds_abs P ι Bw h hj hart hμ hL (hB.isPstAt T Bw _ ?_
    (CharAboveModel.conclusion_absPow P AI ⟨T⟩ ι art hart 1 μ hμ hL A O Bw).1) hξ ha
  refine continuous_matrix fun i j => ?_
  have : Continuous fun g : Dec (F := E) A => ((μ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp (hμ.comp continuous_subtype_val)
  fin_cases i; fin_cases j
  simpa [rk1] using this

theorem ne_inv {x : WD h} {ξ : (w.adicCompletion E)ˣ →* ℂˣ} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {hs hs'} (e : x = WD.lpOfChar h (ξ.comp a) hs) (hξ : ξ ≠ ξ⁻¹) :
    x ≠ WD.lpOfChar h (ξ⁻¹.comp a) hs' := fun e' => by
  have := lpOfChar_inj (e.symm.trans e')
  refine hξ (MonoidHom.ext fun y => ?_)
  obtain ⟨σ, rfl⟩ := ha.surj y
  exact DFunLike.congr_fun this σ

omit [IsAlgClosure E Ω] in

theorem abs_ne_inv : (Model.absPow E (1 : ℕ)).loc w ≠ ((Model.absPow E (1 : ℕ)).loc w)⁻¹ := fun e => by
  have hval := (Model.absPow_isAbsPow E (1 : ℕ)).2.1 w
  have h1 : (Model.absPow E (1 : ℕ)).val w = ((Model.absPow E (1 : ℕ)).val w)⁻¹ :=
    DFunLike.congr_fun e (atFin w (unif w))
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) h1
  simp only [Units.val_inv_eq_inv_val, hval] at h2
  have hq : 1 < Ideal.absNorm w.asIdeal := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using GlobalTheory.WeilDeligne.one_lt_normV w
  simp only [Nat.cast_one, Complex.ofReal_one, Complex.cpow_neg_one, inv_inv] at h2
  have h0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h3 := mul_inv_cancel₀ h0
  rw [h2] at h3
  have h4 : Ideal.absNorm w.asIdeal * Ideal.absNorm w.asIdeal = 1 := by exact_mod_cast h3
  nlinarith

end GlobalTheory.Published.CharWDTest

end
