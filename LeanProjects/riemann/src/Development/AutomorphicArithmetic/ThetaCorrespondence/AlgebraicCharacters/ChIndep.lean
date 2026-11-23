import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
open UpperTheory.Lit.CharWD GlobalTheory.Published

noncomputable section SlopeTestRemainingChoices

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne TensorProduct Module Formalism.WeaklyAdmissibleFiltrations
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

private theorem kummer_ratio (P Q : LocPrime l) :
    ∃ a : ℤ_[l], a ≠ 0 ∧ ∀ g, kummer P g = a * kummer Q g := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ m, ∃ a : ℕ, Q.ζQ m = P.ζQ m ^ a := fun m => by
    obtain ⟨a, -, ha⟩ := (isPrimitiveRoot_zeta P m).eq_pow_of_pow_eq_one (isPrimitiveRoot_zeta Q m).pow_eq_one
    exact ⟨a, ha.symm⟩
  choose a ha using h1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [Q.ζQ_succ] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, P.ζQ_succ, ha i] at h2
    have h3 := (zeta_pow_eq_iff P i _ _).mp h2
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  have key : ∀ g, kummer P g = PadicInt.ofIntSeq (fun i => (a i : ℤ))
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd) * kummer Q g := fun g => by
    refine (isKummer_kummer P g).unique fun m => ?_
    rw [isKummer_kummer Q g m, ha m, ← pow_mul, map_mul, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd]
    congr 1
    rw [zeta_pow_eq_iff]
    simp
  refine ⟨_, fun h0 => ?_, key⟩
  obtain ⟨g, hg⟩ := exists_kummer_ne_zero P
  exact hg (by rw [key, h0, zero_mul])

private theorem exists_cris {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) : ∃ e : P.R.B ≃ₐ[ℚ_[l]] Q.R.B, (∀ g b, e (P.actQ g b) = Q.actQ g (e b)) ∧
      (∀ b, e (P.φB b) = Q.φB (e b)) ∧
      ∀ c, e (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) Q.R.B c := by
  let e₀ : P.R.B ≃+* Q.R.B := TP.eB.trans TQ.eB.symm
  have he : ∀ b, TQ.eB (e₀ b) = TP.eB b := fun b => TQ.eB.apply_symm_apply _
  have hq : (e₀ : P.R.B →+* Q.R.B).comp (algebraMap ℚ_[l] P.R.B) = algebraMap ℚ_[l] Q.R.B := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => TQ.eB.injective ?_)
    exact (he _).trans ((TP.zB z).trans (TQ.zB z).symm)
  let e : P.R.B ≃ₐ[ℚ_[l]] Q.R.B := { e₀ with commutes' := RingHom.congr_fun hq }
  have he' : ∀ b, TQ.eB (e b) = TP.eB b := he
  refine ⟨e, fun g b => TQ.eB.injective ?_, fun b => TQ.eB.injective ?_, fun c => ?_⟩
  · rw [he', TP.actB, TQ.actB, he']
  · rw [he', TP.frob, TQ.frob, he']
  · have : (e : P.R.B →ₐ[ℚ_[l]] Q.R.B).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
        IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) Q.R.B := by
      refine kur_algHom_ext fun c m h0 hm hc => TQ.eB.injective ?_
      have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
      obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m h0 hm hc'
      refine (he' _).trans ?_
      show TP.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = TQ.eB (algebraMap ↥(MaximalUnramifiedExtension l) Q.R.B c)
      rw [← AP.ιA_teich c m h0 hm hc' xb hxb, ← AQ.ιA_teich c m h0 hm hc' xb hxb, TP.ιA, TQ.ιA]
    exact AlgHom.congr_fun this c

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {P Q : LocPrime l} (e : P.R.B ≃ₐ[ℚ_[l]] Q.R.B)
    (ha : ∀ g b, e (P.actQ g b) = Q.actQ g (e b)) : ∃ u : ℚ_[l], u ≠ 0 ∧ e P.tB = u • Q.tB := by
  have hχ : P.χQ = Q.χQ := GlobalTheory.Cyc.TwistLift.isCyc_unique P.χQ_cyc Q.χQ_cyc
  obtain ⟨c, hc⟩ := (Q.PD (botExt l)).invB (e P.tB * tInv Q) fun g => by
    rw [Q.PD_actB, map_mul, ← ha, localPrime_galoisAction_periodT, map_smul, smul_mul_assoc, ← mul_smul_comm, hχ, smul_actQ_tInv]
  obtain ⟨u, hu⟩ := IntermediateField.mem_bot.mp c.2.1
  have h1 : c = algebraMap ℚ_[l] _ u := Subtype.ext hu.symm
  rw [h1, ← IsScalarTower.algebraMap_apply] at hc
  have h2 : e P.tB = u • Q.tB := by
    rw [Algebra.smul_def, hc, mul_assoc, tInv_mul, mul_one]
  refine ⟨u, fun h0 => ?_, h2⟩
  have := nontrivial_B Q
  rw [h0, zero_smul] at h2
  exact ((isUnit_tB P).map e).ne_zero h2

private def stMap {P Q : LocPrime l} (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) (z : ℚ_[l]) : Bst P →ₐ[ℚ_[l]] Bst Q :=
  eval₂AlgHom (CAlgHom.comp e) (z • X) fun _ => Commute.all _ _

private theorem stMap_C {P Q : LocPrime l} (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) (z : ℚ_[l]) (b : P.R.B) :
    stMap e z (C b) = C (e b) := eval₂_C _ _

private theorem stMap_X {P Q : LocPrime l} (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) (z : ℚ_[l]) :
    stMap e z X = z • X := eval₂_X _ _

private theorem stMap_der {P Q : LocPrime l} (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) (z : ℚ_[l]) (p : Bst P) :
    derivative (stMap e z p) = z • stMap e z (derivative p) := by
  have h : ∀ q : Bst P, stMap e z q = (q.map (e : P.R.B →+* Q.R.B)).comp (z • X) := fun q => by
    rw [comp, eval₂_map]; rfl
  rw [h, h, derivative_comp, derivative_map, derivative_smul, derivative_X, smul_mul_assoc, one_mul]

private theorem exists_st {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) : ∃ (E : Bst P ≃ₐ[ℚ_[l]] Bst Q) (z : ℚ_[l]), z ≠ 0 ∧
      (∀ g b, E (actSt P g b) = actSt Q g (E b)) ∧ (∀ b, E (phiSt P b) = phiSt Q (E b)) ∧
      (∀ c, E (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst Q) c) ∧
      ∀ b, E (monSt P b) = z • monSt Q (E b) := by
  obtain ⟨e, h1, h2, h3⟩ := exists_cris TP TQ
  obtain ⟨u, hu, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator e h1
  obtain ⟨a, ha, hk⟩ := kummer_ratio P Q
  have hz : (a : ℚ_[l]) * u ≠ 0 := mul_ne_zero (PadicInt.coe_ne_zero.mpr ha) hu
  set z := (a : ℚ_[l]) * u with hzd
  let E : Bst P ≃ₐ[ℚ_[l]] Bst Q := AlgEquiv.ofAlgHom (stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z)
    (stMap (e.symm : Q.R.B →ₐ[ℚ_[l]] P.R.B) z⁻¹)
    (stHom_ext Q (fun b => by simp [stMap_C]) (by simp [stMap_X, smul_smul, hz]))
    (stHom_ext P (fun b => by simp [stMap_C]) (by simp [stMap_X, smul_smul, hz]))
  have hE : ∀ b, E b = stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z b := fun _ => rfl
  refine ⟨E, z⁻¹, inv_ne_zero hz, fun g b => ?_, fun b => ?_, fun c => ?_, fun b => ?_⟩
  · have : (stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z).comp (actSt P g) =
        (actSt Q g).comp (stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z) := by
      refine algHom_ext' (AlgHom.ext fun b => ?_) ?_
      · simp [stMap_C, h1]
      · have : (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) P.tB = u • Q.tB := ht
        simp only [AlgHom.comp_apply, actSt_X, map_add, stMap_X, stMap_C, map_smul, this, smul_add, smul_C, smul_smul,
          hk, PadicInt.coe_mul, hzd]
        congr 3
        ring
    exact AlgHom.congr_fun this b
  · have : (stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z).comp (phiSt P) =
        (phiSt Q).comp (stMap (e : P.R.B →ₐ[ℚ_[l]] Q.R.B) z) := by
      refine algHom_ext' (AlgHom.ext fun b => ?_) ?_
      · simp [stMap_C, h2]
      · simp [stMap_X]
    exact AlgHom.congr_fun this b
  · rw [hE, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, stMap_C]
    exact congrArg C (h3 c)
  · rw [hE, hE, monSt_apply, monSt_apply, stMap_der, map_neg, smul_neg, inv_smul_smul₀ hz]

private theorem exists_D {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {K : FinExt l} (ρ : Representation LL ↥(GK K) V) :
    ∃ (T : ↥(Dpst P ρ) ≃ₗ[LL] ↥(Dpst Q ρ)) (z : LL), z ≠ 0 ∧ (∀ g x, T (actD P ρ g x) = actD Q ρ g (T x)) ∧
      (∀ x, T (phiD P ρ x) = phiD Q ρ (T x)) ∧ (∀ c x, T (mulD P ρ c x) = mulD Q ρ c (T x)) ∧
      ∀ x, T (monD P ρ x) = z • monD Q ρ (T x) := by
  obtain ⟨E, z, hz, h1, h2, h3, h4⟩ := exists_st TP TQ
  let S : V ⊗[ℚ_[l]] Bst P ≃ₗ[LL] V ⊗[ℚ_[l]] Bst Q :=
    AlgebraTensorModule.congr (LinearEquiv.refl LL V) E.toLinearEquiv
  have hS : ∀ v b, S (v ⊗ₜ b) = v ⊗ₜ E b := fun _ _ => rfl
  have ext : ∀ (f : End LL (V ⊗[ℚ_[l]] Bst P)) (f' : End LL (V ⊗[ℚ_[l]] Bst Q)),
      (∀ v b, S (f (v ⊗ₜ b)) = f' (v ⊗ₜ E b)) → ∀ x, S (f x) = f' (S x) := fun f f' h x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => exact h v b
    | add x y hx hy => simp only [map_add, hx, hy]
  have a1 : ∀ g x, S (stRep P ρ g x) = stRep Q ρ g (S x) := fun g =>
    ext _ _ fun v b => by rw [stRep_tmul, stRep_tmul, hS, h1]
  have a2 := ext (phiV P LL V) (phiV Q LL V) fun v b => by rw [phiV_tmul, phiV_tmul, hS, h2]
  have a3 := fun c => ext (mulV P LL V c) (mulV Q LL V c) fun v b => by
    rw [mulV_tmul, mulV_tmul, hS, map_mul, h3]
  have a4 := ext (monV P LL V) (algebraMap ℚ_[l] LL z • monV Q LL V) fun v b => by
    rw [LinearMap.smul_apply, monV_tmul, monV_tmul, hS, h4, tmul_smul, algebraMap_smul]
  have hmap : (Dpst P ρ).map (S : V ⊗[ℚ_[l]] Bst P →ₗ[LL] V ⊗[ℚ_[l]] Bst Q) = Dpst Q ρ := by
    ext y
    obtain ⟨x, rfl⟩ := S.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_Dpst, mem_Dpst]
    simp only [← a1, S.injective.eq_iff]
  exact ⟨S.ofSubmodules _ _ hmap, algebraMap ℚ_[l] LL z, (_root_.map_ne_zero _).mpr hz,
    fun g x => Subtype.ext (a1 g x.1), fun x => Subtype.ext (a2 x.1), fun c x => Subtype.ext (a3 c x.1),
    fun x => Subtype.ext (a4 x.1)⟩

private theorem isPst_indep {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (hV : IsPst P ρ) : IsPst Q ρ := by
  obtain ⟨T, -, -, -, -, h3, -⟩ := exists_D TP TQ ρ
  let U : DpstUr P ρ ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr Q ρ :=
    { ((toUr P ρ).symm.trans T.toAddEquiv).trans (toUr Q ρ) with map_smul' := fun c x => h3 c x }
  exact U.rank_eq.symm.trans hV

variable (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B)

private theorem map_weilD {P Q : LocPrime l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK B.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr Q ρ)] (T : ↥(Dpst P ρ) → ↥(Dpst Q ρ))
    (t1 : ∀ g x, T (actD P ρ g x) = actD Q ρ g (T x)) (t2 : ∀ x, T (phiD P ρ x) = phiD Q ρ (T x)) (σ x) :
    T (weilD B h P ρ σ x) = weilD B h Q ρ σ (T x) :=
  (t1 _ _).trans (congrArg (actD Q ρ (weilToGK B h σ))
    (BridgeParam.map_zpow_apply T (phiU P ρ) (phiU Q ρ) t2 (-alpha l σ) x))

private theorem wdPst_indep {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) {L : FinExt l}
    {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK B.Kw) V) (hV : IsPst P ρ) :
    wdPst P ι B h hj ρ = wdPst Q ι B h hj ρ := by
  have hV' := isPst_indep TP TQ ρ hV
  have := hV.finite
  have := hV'.finite
  obtain ⟨T, a, ha, t1, t2, t3, hN⟩ := exists_D TP TQ ρ
  have hw := map_weilD B h ρ T t1 t2
  letI := algC ι L
  let Φ : WDSpace P ι ρ →ₗ[ℂ] WDSpace Q ι ρ :=
    EnlargeCoeff.chg (mulD P ρ) (mulD Q ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl)
      T.toAddEquiv.toAddMonoidHom T.map_smul t3
  have hΦ : ∀ x, Φ (wdMk P ι ρ x) = wdMk Q ι ρ (T x) := fun x => EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ _ _
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk Q ι ρ, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact ⟨_, (hΦ (T.symm y)).trans (by rw [T.apply_symm_apply])⟩
  have hd : finrank ℂ (WDSpace P ι ρ) = finrank ℂ (WDSpace Q ι ρ) := by
    rw [LetterDim.finrank_wdSpace l P ι B.Kw L _ _ hV, LetterDim.finrank_wdSpace l Q ι B.Kw L _ _ hV']
  let e := LinearEquiv.ofBijective Φ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩
  have h1 : ∀ σ v, e (wdRho P ι B h hj ρ σ v) = wdRho Q ι B h hj ρ σ (e v) := fun σ v => by
    have : Φ.comp (wdRho P ι B h hj ρ σ) = (wdRho Q ι B h hj ρ σ).comp Φ :=
      LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
        simp only [LinearMap.comp_apply, wdRho_mk, hΦ, hw]
    exact LinearMap.congr_fun this v
  have h2 : ∀ v, e (wdN P ι ρ v) = (ι (a : Om l) • wdN Q ι ρ) (e v) := fun v => by
    have : Φ.comp (wdN P ι ρ) = (ι (a : Om l) • wdN Q ι ρ).comp Φ :=
      LinearMap.ext_on_range (span_wdMk P ι ρ) fun x => by
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, wdN_mk, hΦ, hN, wdMk_smul]
    exact LinearMap.congr_fun this v
  have ha' : ι (a : Om l) ≠ 0 := (_root_.map_ne_zero ι).mpr fun h0 => ha (Subtype.ext h0)
  rw [wdPst_of_isPst ι B h hj hV, wdPst_of_isPst ι B h hj hV']
  exact WD.sound (BridgeParam.iso_of_equiv_smul h (BridgeParam.isFrobSS_wdRep P ι B h hj ρ)
    (BridgeParam.isFrobSS_wdRep Q ι B h hj ρ)
    (isSmooth_wdRho Q ι B h hj ρ) (isNilpotent_wdN Q ι ρ) (wdRho_wdN Q ι B h hj ρ) e ha' h1 h2)

private theorem wdAt_model (P : LocPrime l) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdAt_indep {P Q : LocPrime l} {AP : LocAinf l P} {AQ : LocAinf l Q} (TP : LocTied l P AP)
    (TQ : LocTied l Q AQ) {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (hr : IsPstAt P B r) :
    IsPstAt Q B r ∧ wdAt Q ι B h hj r = wdAt P ι B h hj r := by
  obtain ⟨L, r', hm, hV⟩ := hr
  have hV' := isPst_indep TP TQ _ hV
  refine ⟨⟨L, r', hm, hV'⟩, ?_⟩
  rw [wdAt_model ι B h hj P r L r' hm hV, wdAt_model ι B h hj Q r L r' hm hV', wdPst_indep ι B h hj TP TQ _ hV]

end SlopeTestRemainingChoices

theorem UpperTheory.Lit.CharWD.chIndep :
    ChIndep := by
  intro F Ω _ _ _ _ _ l _ A w P AI ⟨TP⟩ ι h O _ _ _ Bw hj κ ξ _ ⟨h1, hs, h2⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨h3, h4⟩ := wdAt_indep ι Bw h hj T TP _ h1
  exact ⟨h3, hs, h4.trans h2⟩
