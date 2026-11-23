import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
open private ex_bridge from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
open UpperTheory.Lit.CharWD GlobalTheory.Published

section SlopeTestRemainingChoices
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.WeilRestrict Module

private theorem wdAt_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
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

private theorem alpha_res {F F' Ω : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Field Ω]
    [Algebra F F'] [Algebra F Ω] [Algebra F' Ω] [IsScalarTower F F' Ω] [IsAlgClosure F Ω] [IsAlgClosure F' Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {w' : HeightOneSpectrum (𝓞 F')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (hw : w ∈ placesOver F l) (hw' : w' ∈ placesOver F' l)
    (σ : Weil h') : alpha l (resWeil h h' σ) = alpha l σ := by
  obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
  obtain ⟨a, b, hab⟩ := σ.2
  have h1 := deg_eq hab
  rw [hf] at hab
  have h2 := deg_eq (σ := resWeil h h' σ) (actsAs_resG (K := F) hab)
  have h3 : resDeg l w' = resDeg l w * f := by
    rw [normV_eq_pow hw, normV_eq_pow hw', ← pow_mul] at hf
    exact Nat.pow_right_injective (Fact.out : l.Prime).two_le hf
  rw [alpha, alpha, h1, h2, h3]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
private theorem eig_res {F F' Ω : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Field Ω]
    [Algebra F Ω] [Algebra F' Ω] [IsAlgClosure F Ω] [IsAlgClosure F' Ω]
    {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {w' : HeightOneSpectrum (𝓞 F')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
    {O O' : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (B : LocBridge l F Ω (Dec (F := F) A) O) (B' : LocBridge l F' Ω (Dec (F := F') A) O')
    (hj : Induces B) (hj' : Induces B') (hK : B.Kw.1 ≤ B'.Kw.1)
    {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK B.Kw) V) (hV : IsPst P ρ)
    (σ : Weil h) (σ' : Weil h') (h1 : weilToGK B h σ = Subgroup.inclusion (GK_le hK) (weilToGK B' h' σ'))
    (h2 : alpha l σ = alpha l σ') :
    (wdPst P ι B' h' hj' (resTo ρ hK)).eig σ' = (wdPst P ι B h hj ρ).eig σ := by
  have hV' : IsPst P (resTo ρ hK) := (GlobalTheory.PstLaws.isPst_resTo_iff P ρ hK).2 hV
  haveI := hV.finite
  haveI := hV'.finite
  letI := algC ι L
  let T : ↥(Dpst P (resTo ρ hK)) →ₗ[↥L.1] ↥(Dpst P ρ) := Submodule.inclusion (Dpst_resTo P ρ hK).le
  let Φ : WDSpace P ι (resTo ρ hK) →ₗ[ℂ] WDSpace P ι ρ :=
    EnlargeCoeff.chg (mulD P (resTo ρ hK)) (mulD P ρ) ℂ (urC ι) (RingHom.id _) (fun _ => rfl) T.toAddMonoidHom
      (fun a x => T.map_smul a x) (fun _ _ => rfl)
  have hΦ : ∀ x, Φ (wdMk P ι (resTo ρ hK) x) = wdMk P ι ρ (T x) := fun x => EnlargeCoeff.chg_mk _ _ _ _ _ _ _ _ _ _
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact ⟨_, hΦ ⟨y.1, (Dpst_resTo P ρ hK).ge y.2⟩⟩
  have hd : finrank ℂ (WDSpace P ι (resTo ρ hK)) = finrank ℂ (WDSpace P ι ρ) := by
    rw [LetterDim.finrank_wdSpace l P ι B.Kw L _ _ hV, LetterDim.finrank_wdSpace l P ι B'.Kw L _ _ hV']
  let e := LinearEquiv.ofBijective Φ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hsurj, hsurj⟩
  have hw : ∀ x, T (weilD B' h' P (resTo ρ hK) σ' x) = weilD B h P ρ σ (T x) := fun x => by
    rw [weilD_apply, weilD_apply, End.mul_apply, End.mul_apply, h1, h2,
      ← BridgeParam.map_zpow_apply T (phiU P (resTo ρ hK)) (phiU P ρ) (fun _ => rfl)]
    rfl
  have h3 : Φ.comp (wdRho P ι B' h' hj' (resTo ρ hK) σ') = (wdRho P ι B h hj ρ σ).comp Φ :=
    LinearMap.ext_on_range (span_wdMk P ι _) fun x => by
      simp only [LinearMap.comp_apply, wdRho_mk, hΦ, hw]
  have h4 : wdRho P ι B h hj ρ σ = e.conj (wdRho P ι B' h' hj' (resTo ρ hK) σ') := LinearMap.ext fun v => by
    obtain ⟨v, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    exact (LinearMap.congr_fun h3 v).symm
  rw [wdPst_of_isPst ι B h hj hV, wdPst_of_isPst ι B' h' hj' hV', WD.eig_mk, WD.eig_mk,
    (BridgeParam.isFrobSS_wdRep P ι B h hj ρ).charpoly_eq, (BridgeParam.isFrobSS_wdRep P ι B' h' hj' _).charpoly_eq,
    h4, LinearEquiv.charpoly_conj]

end SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst
  GlobalTheory.WeilRestrict GlobalTheory.TripleGal UpperTheory.V in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.Lit.CharWD.chRes :
    ChRes := by
  intro F F' Ω _ _ _ _ _ _ _ _ _ _ _ l _ A w w' ι h h' O _ _ _ Bw hj
  obtain ⟨L', Bw', hBj⟩ := ex_bridge (E := F') (A := A) Bw.j hj
  have hj' : Induces Bw' := fun x => by rw [hBj]; exact hj x
  refine ⟨↥(OL L'), inferInstance, inferInstance, inferInstance, Bw', hj', fun κ κ' _ hκ ξ hξ => ?_⟩
  obtain ⟨⟨L₀, r₀, hm₀, hV₀⟩, hs, hξ⟩ := hξ
  have hK : Bw.Kw.1 ≤ Bw'.Kw.1 := by
    rw [BridgeInd.kw_eq_adjoin Bw, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    have := Bw'.j_E (algebraMap F F' x)
    rwa [hBj, ← IsScalarTower.algebraMap_apply] at this
  have hL₀ : L₀.1 ≤ (supExt L₀ Bw'.LL).1 := le_sup_left
  have hL : Bw'.LL.1 ≤ (supExt L₀ Bw'.LL).1 := le_sup_right
  obtain ⟨r₁, hm, hV⟩ : ∃ r₁, IsModel Bw (rk1 κ) (supExt L₀ Bw'.LL) r₁ ∧
      IsPst (Loc.PP l) (Bw.repE (supExt L₀ Bw'.LL) r₁) :=
    ⟨_, ⟨hm₀.1.trans hL₀, by rw [← hm₀.2]; rfl⟩, GlobalTheory.PstExt.isPst_enlarge _ Bw hL₀ r₀ hV₀⟩
  generalize supExt L₀ Bw'.LL = L at hL r₁ hm hV
  let f : ↥(Dec (F := F') A) →* ↥(Dec (F := F) A) :=
    ((resG F).comp (Dec (F := F') A).subtype).codRestrict _ fun σ => resG_mem_Dec σ.2
  have hκ' : κ' = κ.comp f := MonoidHom.ext fun g => (hκ (f g) g fun _ => rfl).symm
  have hm' : IsModel Bw' (rk1 κ') L (r₁.comp f) :=
    ⟨hL, MonoidHom.ext fun g => by rw [hκ']; exact DFunLike.congr_fun hm.2 (f g)⟩
  have hg : ∀ g, f (Bw'.e.symm g) = Bw.e.symm (Subgroup.inclusion (GK_le hK) g) := fun g => by
    refine Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)
    have a1 := Bw'.e_comm (Bw'.e.symm g) x
    have a2 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le hK) g)) x
    rw [MulEquiv.apply_symm_apply] at a1 a2
    rw [hBj] at a1
    exact a1.symm.trans a2
  have hrep : Bw'.repE L (r₁.comp f) = resTo (Bw.repE L r₁) hK :=
    MonoidHom.ext fun g =>
      congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin 1) (Fin 1) ↥L.1)) (hg g)
  have hV' : IsPst (Loc.PP l) (Bw'.repE L (r₁.comp f)) := by
    rw [hrep]; exact (GlobalTheory.PstLaws.isPst_resTo_iff _ _ hK).2 hV
  haveI : Algebra.IsIntegral F' Ω := (IsAlgClosure.isAlgebraic (R := F') (K := Ω)).isIntegral
  refine ⟨ξ.comp (resWeil h h'), ⟨⟨L, _, hm', hV'⟩, isSmooth_comp_resWeil h h' hs, ?_⟩, fun σ σ' H => ?_⟩
  · refine ParamAboveModel.eq_lpOfChar h' _ (GlobalTheory.Pst.Test.lpDim_wdAt _ ι Bw' h' hj' _) _ _ fun σ => ?_
    have h1 : weilToGK Bw h (resWeil h h' σ) = Subgroup.inclusion (GK_le hK) (weilToGK Bw' h' σ) := by
      have h2 := hg (weilToGK Bw' h' σ)
      rw [eq_comm, MulEquiv.symm_apply_eq] at h2
      rw [h2]
      exact congrArg (fun s => Bw.e (f s)) (Bw'.e.symm_apply_apply (Subgroup.inclusion (Weil_le_Dec h') σ)).symm
    rw [wdAt_model _ ι Bw' h' hj' _ L _ hm' hV', hrep,
      eig_res _ ι h h' Bw Bw' hj hj' hK _ hV _ σ h1 (alpha_res h h' (hj.mem_placesOver h) (hj'.mem_placesOver h') σ),
      ← wdAt_model _ ι Bw h hj _ L _ hm hV, hξ, GlobalTheory.LocLanglands.eig_lpOfChar]
    exact Multiset.mem_singleton_self _
  · exact congrArg ξ (Subtype.ext (AlgEquiv.ext H))
