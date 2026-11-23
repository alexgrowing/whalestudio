import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RankOneCharacterIsdRAndJumpsZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfIsNilpotentOfFinrankEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section

open GlobalTheory.Pst GlobalTheory.TripleGal

private theorem potCrys_of_dR (hB : DeRhamPotSemistable) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [Fact l.Prime] {Gw : Subgroup (Ω ≃ₐ[F] Ω)} (κ : ↥Gw →* (Qbar l)ˣ) (hκ : Continuous κ)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω Gw O)
    (hd : IsdRAt (UpperTheory.V.Loc.PP l) Bw (rk1 κ)) : IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw (rk1 κ) := by
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨LL', r', hm, hp⟩ := hB.isPstAt T Bw _ (GlobalTheory.CharAboveRead.continuous_rankOneOperator κ hκ) hd
  haveI := hp.finite
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have h1 : Module.finrank ℂ (WDSpace (UpperTheory.V.Loc.PP l) ι (Bw.repE LL' r')) = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l _ ι _ LL' _ _ hp, Module.finrank_fin_fun]
  have hN : wdN (UpperTheory.V.Loc.PP l) ι (Bw.repE LL' r') = 0 :=
    GlobalTheory.PotCrysRankOne.eq_zero_of_isNilpotent_of_finrank_eq_one h1 (isNilpotent_wdN _ ι _)
  obtain ⟨K', hK, hcr⟩ := (GlobalTheory.PstLaws.isPotCrys_iff _ _ hp).2 ((GlobalTheory.PstLaws.wdN_eq_zero_iff _ _ ι).1 hN)
  exact ⟨LL', r', hm, K', hK, hcr⟩

private theorem bridge_transfer {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F Ω]
    [Algebra E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[F] Ω)} {Gu : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω Gw O)
    (Bw' : LocBridge l E Ω Gu O) (hK : Bw'.Kw = Bw.Kw) (hj : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL) {n : ℕ}
    (r : ↥Gw →* GL (Fin n) (Om l)) (r' : ↥Gu →* GL (Fin n) (Om l))
    (hr : ∀ (g : ↥Gw) (g' : ↥Gu), (∀ z, (g : G F Ω) z = (g' : G E Ω) z) → r g = r' g') (hd : IsdRAt P Bw' r') :
    IsdRAt P Bw r ∧ ∀ (τ : F →+* Om l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1), IsInduced Bw τ τ' →
      ∃ (τE : E →+* Om l) (τ₂ : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥Bw'.LL.1), IsInduced Bw' τE τ₂ ∧
        (∀ (x : E) (hx : Bw.j (algebraMap E Ω x) ∈ Bw.Kw.1),
          τE x = ((τ' ⟨Bw.j (algebraMap E Ω x), hx⟩ : ↥Bw.LL.1) : Om l)) ∧
        ∀ J, IsJumpsAt P Bw' r' τE J → IsJumpsAt P Bw r τ J := by
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  set Bw' : LocBridge l E Ω Gu O :=
    ⟨Bw.Kw, Bw.j, jE', jd', e', ec', esc', ecomm', Bw.LL, hs', eO', h1', h2', h3'⟩ with hB
  obtain ⟨L, r₀, hm, hV⟩ := hd
  let r₁ : ↥Gw →* GL (Fin n) ↥L.1 := r₀.comp (Bw.e.trans e'.symm).toMonoidHom
  have hm₁ : IsModel Bw r L r₁ := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    refine (DFunLike.congr_fun hm.2 (e'.symm (Bw.e g))).trans (hr _ _ fun z => Bw.j.injective ?_).symm
    rw [← ecomm', MulEquiv.apply_symm_apply, Bw.e_comm]
  have hrep : Bw.repE L r₁ = Bw'.repE L r₀ := by
    refine MonoidHom.ext fun g => ?_
    simp [LocBridge.repE, r₁, hB]
    rfl
  have hV₁ : Bw.IsdRE P L r₁ := by
    unfold LocBridge.IsdRE at hV ⊢
    rw [hrep]
    exact hV
  refine ⟨⟨L, r₁, hm₁, hV₁⟩, fun τ τ' hτ => ⟨(Bw.LL.1.val.comp τ').toRingHom.comp
    ((Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 jE'), τ', fun _ => rfl, fun _ _ => rfl, fun J hJ => ?_⟩⟩
  refine ⟨L, r₁, hm₁, hV₁, (IntermediateField.inclusion hm.1).comp τ', hτ, fun a => ?_⟩
  rw [hJ.count_eq P hm (τ' := (IntermediateField.inclusion hm.1).comp τ') (fun _ => rfl) a]
  unfold LocBridge.multE
  rw [hrep]

end

theorem UpperTheory.V.Loc.laDeRham :
    GlobalArtinReciprocity → HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ wt : Emb l w → ℤ, IsLocAlg h κ wt → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw), GlobalTheory.Pst.IsdRAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) ∧ GlobalTheory.Pst.IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) ∧ ∀ τ : Emb l w, GlobalTheory.Pst.IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) (τ.1.comp (algebraMap F (w.adicCompletion F))) {wt τ} := by
  intro hG hH hD hB F Ω _ _ _ _ _ l _ A w h κ hκ wt ⟨ph, hph⟩ O _ _ _ Bw hj
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨E, _, _, _, _, u, hu, Bw', art, χ, n, μ, ν, b1, b2, b3, hart, hχ, hμ, hL, hν, hνμ, ⟨ph', hph'⟩, hn⟩ :=
    laGlob hG hH h wt Bw hj ι
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [b2]; exact hj x
  obtain ⟨d1, d2⟩ := hD E Ω l _ _ (tiedP l) ι art hart χ n μ hχ hμ hL u A hu O Bw' hj'
  obtain ⟨c1, c2⟩ := bridge_transfer (PP l) Bw Bw' b1 b2 b3 (GlobalTheory.TripleGal.rk1 ν)
    ((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := E) A).subtype)
    (fun g g' hg => congrArg (Units.map (Matrix.scalar (Fin 1) : Qbar l →+* _).toMonoidHom) (hνμ g g' hg)) d1
  have h0 := ((laMul h).1 _ _ _ _ _ _ hph ((laMul h).1 _ _ _ _ _ _ hph' hph').2).1
  rw [add_neg_cancel] at h0
  obtain ⟨a, ha⟩ := laArtin hG h
  have ho : IsOpen {σ : ↥(Ine (F := F) A) | (κ * ν⁻¹) (Subgroup.inclusion (Ine_le_Dec A) σ) = 1} := by
    refine Subgroup.isOpen_mono (H₁ := (ph * ph'⁻¹).ker)
      (H₂ := ((κ * ν⁻¹).comp (Subgroup.inclusion (Ine_le_Dec A))).ker) (fun σ hσ => ?_) h0.1
    have := h0.2 a ha σ
    rw [MonoidHom.mem_ker.1 hσ, mul_one] at this
    rw [show (∏ᶠ τ : Emb l w, τ.1 (a (ineIncl h σ) : w.adicCompletion F) ^ (-(0 : Emb l w → ℤ) τ)) = 1 by simp] at this
    exact Units.ext this
  obtain ⟨u1, u2⟩ := UpperTheory.rankOne_character_isdR_and_jumps_zero (κ * ν⁻¹) (hκ.mul hν.inv) ho O Bw hj
  obtain ⟨t1, -, -, t2⟩ := GlobalTheory.TwistAbove.twist_above l _ _ (tiedP l) F Ω _ O Bw 1 (GlobalTheory.TripleGal.rk1 ν) (GlobalTheory.TripleGal.rk1 κ)
    (κ * ν⁻¹) (fun g => by
      ext i j
      simp [GlobalTheory.TripleGal.rk1, Subsingleton.elim i j])
  refine ⟨t1 c1 u1, potCrys_of_dR hB κ hκ Bw (t1 c1 u1), fun τ => ?_⟩
  obtain ⟨τ', hτ'⟩ := exists_isInduced_emb h Bw hj τ
  obtain ⟨τE, τ₂, e1, e2, e3⟩ := c2 _ τ' hτ'
  have := t2 _ _ 0 (e3 _ (d2 τE _ τ₂ e1)) (u2 _ _ τ' hτ')
  rw [hn τ (Bw.LL.1.val.comp τ') τE hτ' e2] at this
  simpa using this
