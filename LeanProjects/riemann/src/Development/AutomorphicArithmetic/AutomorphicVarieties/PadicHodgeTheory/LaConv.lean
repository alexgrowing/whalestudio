import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaDeRham
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MulMemDeRhamPeriodFiltrationOfMemZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DdRLeFilAndInfFilEqBotOfHodgeTateMult
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc.LaConv

open GlobalTheory.Pst GlobalTheory.TripleGal Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

private theorem norm_lt (j : Emb l w) (y : w.adicCompletion F) (hy : Valued.v y < 1) : ‖j.1 y‖ < 1 := by
  have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hy)
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact h3.congr fun n => by simp

private theorem norm_le (j : Emb l w) {π : w.adicCompletion F} (h0 : π ≠ 0) (hπ : Valued.v π < 1)
    (y : w.adicCompletion F) (hy : Valued.v y = 1) : ‖j.1 y‖ ≤ 1 := by
  have hpos : 0 < ‖j.1 π‖ := norm_pos_iff.mpr ((map_ne_zero j.1).mpr h0)
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖j.1 π‖⁻¹) (not_le.1 hlt)
  have h4 := norm_lt j (π * y ^ n) (by rwa [map_mul, map_pow, hy, one_pow, mul_one])
  rw [map_mul, map_pow, norm_mul, norm_pow] at h4
  rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
  exact lt_asymm hn h4

private theorem exists_char (wt : Emb l w → ℤ) : ∃ ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ, Continuous ξ ∧
    (∀ x, ‖(ξ x : Qbar l)‖ = 1) ∧ ∀ x : (w.adicCompletion F)ˣ, Valued.v (x : w.adicCompletion F) = 1 →
      (ξ x : Qbar l) = ∏ᶠ τ : Emb l w, τ.1 (x : w.adicCompletion F) ^ wt τ := by
  haveI := finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (Emb l w)
  obtain ⟨p, hp⟩ := w.valuation_exists_uniformizer F
  have hv : Valued.v (algebraMap F (w.adicCompletion F) p) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w p).trans hp
  have h0 : algebraMap F (w.adicCompletion F) p ≠ 0 := fun e => by
    rw [e, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) p) < 1 := by
    rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  let π : (w.adicCompletion F)ˣ := Units.mk0 _ h0
  let n : (w.adicCompletion F)ˣ → ℤ := fun x => WithZero.log (Valued.v (x : w.adicCompletion F))
  have hne : ∀ x : (w.adicCompletion F)ˣ, Valued.v (x : w.adicCompletion F) ≠ 0 := fun x =>
    (map_ne_zero _).2 x.ne_zero
  let u : (w.adicCompletion F)ˣ →* (w.adicCompletion F)ˣ := MonoidHom.mk' (fun x => x * π ^ n x) fun x y => by
    have : n (x * y) = n x + n y := by
      simp only [n, Units.val_mul, map_mul, WithZero.log_mul (hne x) (hne y)]
    rw [this, zpow_add, mul_mul_mul_comm]
  have hu : ∀ x, Valued.v (u x : w.adicCompletion F) = 1 := fun x => by
    change Valued.v ((x * π ^ n x : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hv, ← WithZero.exp_zsmul,
      ← WithZero.exp_log (hne x), ← WithZero.exp_add]
    simp [n]
  have hn : IsLocallyConstant n := (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
    filter_upwards [Units.continuous_val.continuousAt.preimage_mem_nhds (Valued.locally_const (hne x))] with y hy
    exact congrArg WithZero.log hy
  have huc : Continuous u := continuous_id.mul (hn.comp fun m => π ^ m).continuous
  let α : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := ∏ τ : Emb l w, (Units.map τ.1.toMonoidHom) ^ wt τ
  have hα : ∀ x, α x = ∏ τ : Emb l w, (Units.map τ.1.toMonoidHom x) ^ wt τ := fun x => by
    simp only [α, MonoidHom.finsetProd_apply, MonoidHom.zpow_apply]
  have hα' : ∀ x, (α x : Qbar l) = ∏ τ : Emb l w, τ.1 (x : w.adicCompletion F) ^ wt τ := fun x => by
    rw [hα, Units.coe_prod]
    simp
  have hαc : Continuous α := by
    rw [show (α : _ → _) = _ from funext hα]
    exact continuous_finset_prod _ fun τ _ => (Continuous.units_map τ.1.toMonoidHom τ.2).zpow _
  refine ⟨α.comp u, hαc.comp huc, fun x => ?_, fun x hx => ?_⟩
  · rw [MonoidHom.comp_apply, hα', norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    have a1 := norm_le τ h0 h1 _ (hu x)
    have a2 := norm_le τ h0 h1 (u x : w.adicCompletion F)⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero τ.1).2 (u x).ne_zero))] at a2
    rw [norm_zpow, le_antisymm a1 a2, one_zpow]
  · have : u x = x := by
      have h2 : n x = 0 := (congrArg WithZero.log hx).trans WithZero.log_one
      have h3 : u x = x * π ^ n x := rfl
      rw [h3, h2, zpow_zero, mul_one]
    rw [MonoidHom.comp_apply, this, hα', finprod_eq_prod_of_fintype]

end Char

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F}

private theorem exists_wt (H : GlobalArtinReciprocity) (h : IsPlaceOver A w)
    {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (wt : Emb l w → ℤ) :
    ∃ κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ, Continuous κ ∧ IsWtPart h κ (-wt) 1 := by
  obtain ⟨ξ, hξ, hn, hu⟩ := exists_char wt
  obtain ⟨κ, ⟨hc, hκ⟩, -⟩ := laExists H h a ha ξ hξ hn
  refine ⟨κ, hc, by simp, fun a' ha' σ => ?_⟩
  obtain ⟨art, hart⟩ := H F Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  obtain rfl : a' = a := MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  have h2 := ha.ord_eq (ineIncl h σ)
  rw [deg_ineIncl, neg_zero] at h2
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h3 := (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
    (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
  rw [MonoidHom.one_apply, mul_one, hκ, hu _ h3]
  simp only [Pi.neg_apply, neg_neg]

private theorem mem_Iq {j : Ω →+* Om l} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (g : G F Ω) (σ : GQ l)
    (hi : ∀ y, σ (j y) = j (g y)) (h : g ∈ Ine (F := F) A) : σ ∈ Iq l := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hadd : ∀ a b : Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  rw [(iqBasic l).2.2.1]
  intro x hx
  obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hjy : ‖j y‖ ≤ 1 := by
    have e : j y = x + -(x - j y) := by ring
    rw [e]
    exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  have hgy : ‖σ (j y) - j y‖ < 1 := by
    rw [hi, ← map_sub, GlobalTheory.DecLocal.norm_lt_one_iff A j hj]
    exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
  have e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y)) := by
    rw [map_sub]; ring
  rw [e]
  refine (hadd _ _).trans_lt (max_lt (by rw [GlobalTheory.PlaceBridge.norm_algEquiv]; exact hy)
    ((hadd _ _).trans_lt (max_lt hgy ?_)))
  rw [norm_neg]; exact hy

private theorem rep_zero (H : DeRhamPotSemistable) {K L : FinExt l}
    (hs : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L.1) {n : ℕ}
    (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1)) (hc : ReciprocityTheory.Gal.ContAction ρ) (hd : IsDR ((PP l).PD K) ρ)
    (hfin : FiniteDimensional ↥L.1 ↥(DdR ((PP l).PD K) ρ))
    (hm : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c ≠ 0 → multV ((PP l).PD K) ρ τ c = 0) :
    ∃ U : Subgroup ↥(GK K), IsOpen (U : Set ↥(GK K)) ∧ ∀ g ∈ U, (g : GQ l) ∈ Iq l → ρ g = 1 := by
  haveI := K.2
  haveI := L.2
  haveI : IsModuleTopology ℚ_[l] (Fin n → ↥L.1) := isModuleTopologyOfFiniteDimensional
  have hφ : IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  obtain ⟨k1, k2⟩ := UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult (PP l) hs ρ hfin
  have hD : Ddr (GK K).subtype ρ = DdR ((PP l).PD K) ρ := by
    unfold Ddr DdR
    refine iInf_congr fun g => ?_
    have : UpperTheory.V.Loc.actD (GK K).subtype ρ g = actVdR ((PP l).PD K) ρ g := by
      unfold UpperTheory.V.Loc.actD actVdR
      congr 1
      exact LinearMap.ext fun b => ((PP l).PD_actdR K g b).symm
    rw [this]
  have hF : ∀ i, FilT ↥L.1 (Fin n → ↥L.1) i = FilV ((PP l).PD K) (LL := ↥L.1) (V := Fin n → ↥L.1) i := fun i => by
    have : (((PP l).PD (botExt l)).Fil i).restrictScalars ℚ_[l] = (((PP l).PD K).Fil i).restrictScalars ℚ_[l] :=
      SetLike.coe_injective ((PP l).PD_Fil _ _ i)
    unfold FilT FilV
    rw [this]
  refine drWt0 H (GK K).subtype hφ ρ hc
    ((isCrIff K ρ).2.2 ((GlobalTheory.PstCoeff.isDR_resQ_iff (PP l) ρ).2 hd)) ?_ ?_
  · rw [FilD, hD, hF]
    exact inf_eq_left.2 (k1 0 fun τ c hc => hm τ c hc.ne)
  · rw [FilD, hD, hF]
    exact k2 0 fun τ c hc => hm τ c hc.ne'

private theorem char_zero (H : DeRhamPotSemistable) (h : IsPlaceOver A w) (η : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hη : Continuous η) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (hJ : ∀ τ : Emb l w, IsJumpsAt (PP l) Bw (rk1 η) (τ.1.comp (algebraMap F (w.adicCompletion F))) {0}) :
    IsOpen ((η.comp ((Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h))).ker : Set ↥(Ine (F := F) A)) := by
  have key : ∀ (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), ∃ τ : Emb l w,
      IsInduced Bw (τ.1.comp (algebraMap F (w.adicCompletion F))) τ' := fun L τ' => by
    let t : F →+* Om l := (L.1.val.comp τ').toRingHom.comp ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)
    have ht : IsInduced Bw t τ' := fun _ => rfl
    obtain ⟨J, hJ, e, -⟩ := KStar.IdealValuations.exists_completion_map w t (ht.norm_lt_one_iff h hj)
    exact ⟨⟨J, hJ⟩, fun x => (e x).trans (ht x)⟩
  obtain ⟨τ₀, -⟩ := key Bw.Kw (AlgHom.id _ _)
  obtain ⟨L, r, hm, hd, -⟩ := hJ τ₀
  have hval : ∀ g, ((r g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 : Om l) = η g := fun g => by
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) =>
      ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) hm.2
    simpa [mapRep, rk1] using this
  have hc' : Continuous fun g => ((r g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) := by
    refine continuous_matrix fun i j => continuous_induced_rng.2 ?_
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact (Units.continuous_val.comp hη).congr fun g => (hval g).symm
  obtain ⟨U, hU, hU'⟩ := rep_zero H (fun τ y => hm.1 (Bw.LL_split τ y)) (Bw.repE L r)
    ((hc'.comp (Bw.e_symm_cont.comp continuous_fst)).matrix_mulVec continuous_snd)
    ((GlobalTheory.TwistAbove.isDR_iff Bw _ r).2 hd) (finiteDimensional_DdR _ _ hd) fun τ' c hc => by
      obtain ⟨τ, hτ⟩ := key L τ'
      have h1 := IsJumpsAt.count_eq (PP l) hm hτ (hJ τ) c
      rw [Multiset.count_eq_zero.2 (by simpa using hc)] at h1
      exact h1.symm
  let i : ↥(Ine (F := F) A) →* ↥(Dec (F := F) A) := Subgroup.inclusion (Ine_le_Dec A)
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  refine Subgroup.isOpen_mono (H₁ := U.comap (Bw.e.toMonoidHom.comp i)) (fun σ hσ => ?_)
    (hU.preimage (Bw.e_cont.comp hi))
  have h1 := hU' _ hσ (mem_Iq hj (σ : G F Ω) _ (Bw.e_comm (i σ)) σ.2)
  have h2 : (r (Bw.e.symm (Bw.e (i σ))) : Matrix (Fin 1) (Fin 1) ↥L.1).mulVec (fun _ => 1) 0 = 1 :=
    congrFun (LinearMap.congr_fun h1 fun _ => 1) 0
  rw [MulEquiv.symm_apply_apply] at h2
  refine Units.ext ((hval (i σ)).symm.trans ?_)
  simpa [Matrix.mulVec, dotProduct] using h2

end UpperTheory.V.Loc.LaConv

open UpperTheory.V.Loc.LaConv in
theorem UpperTheory.V.Loc.laConv :
    GlobalArtinReciprocity → HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (wt : Emb l w → ℤ), (∀ τ : Emb l w, GlobalTheory.Pst.IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) (τ.1.comp (algebraMap F (w.adicCompletion F))) {wt τ}) → IsLocAlg h κ wt := by
  intro H1 H2 H3 H4 F Ω _ _ _ _ _ l _ A w h κ hκ O _ _ _ Bw hj wt hJ
  by_cases hex : ∃ a, IsLocalArtin h a
  swap
  · exact ⟨1, by simp, fun a ha => absurd ⟨a, ha⟩ hex⟩
  obtain ⟨a, ha⟩ := hex
  obtain ⟨κ₀, hc, hw⟩ := exists_wt H1 h ha wt
  have h0 := (laDeRham H1 H2 H3 H4 h κ₀ hc _ ⟨1, hw⟩ O Bw hj).2.2
  have h1 := char_zero H4 h (κ * κ₀) (hκ.mul hc) Bw hj fun τ => by
    have := (GlobalTheory.TwistAbove.twist_above l (PP l) (AIP l) (tiedP l) F Ω _ O Bw 1 (GlobalTheory.TripleGal.rk1 κ)
      (GlobalTheory.TripleGal.rk1 (κ * κ₀)) κ₀ (fun g => by
        ext i j
        simp [GlobalTheory.TripleGal.rk1, Matrix.diagonal_apply, mul_comm])).2.2.2 _ _ _ (hJ τ) (h0 τ)
    simpa using this
  have h2 := (laMul h).2.2 (κ * κ₀) ((κ * κ₀).comp ((Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)))⁻¹
    (Subgroup.isOpen_mono (fun σ hσ => inv_eq_one.2 hσ) h1) fun σ => mul_inv_cancel _
  have h3 := ((laMul h).1 _ _ _ _ _ _ h2 ((laMul h).1 _ _ _ _ _ _ hw hw).2).1
  rw [mul_inv_cancel_right, neg_neg, zero_add] at h3
  exact ⟨_, h3⟩
