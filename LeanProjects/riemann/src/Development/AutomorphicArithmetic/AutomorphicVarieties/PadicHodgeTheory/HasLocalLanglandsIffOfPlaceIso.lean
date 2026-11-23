import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section SlopeTestRemainingChoices
open Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N Polynomial GlobalTheory.Pst UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
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

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

private theorem eig_of_wdRel {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} {φ : Ω ≃+* Ω'}
    {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hσ : WeilRel φ σ σ') :
    y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, H⟩ := H
  rw [WD.eig_mk, WD.eig_mk, H σ σ' hσ]

set_option maxHeartbeats 1000000 in
private theorem exists_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) :
    ∃ t : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A), Continuous t ∧
      (∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((t g : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x) ∧
      ∀ (n : ℕ) (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw r →
        IsPstAt (Loc.PP l) Bw' (r.comp t) ∧
          WDRel (RingEquiv.refl Ω) (wdAt (Loc.PP l) ι Bw h hj r) (wdAt (Loc.PP l) ι Bw' h' hj' (r.comp t)) := by
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  refine ⟨(e.trans Bw.e.symm).toMonoidHom, Bw.e_symm_cont.comp e_cont, key, fun n r hr => ?_⟩
  obtain ⟨L, r', hm, hV⟩ := hr
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' (r.comp (e.trans Bw.e.symm).toMonoidHom) L r'' :=
    ⟨hm.1, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (Bw.e.symm (e g))⟩
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst (Loc.PP l) (Bw'.repE L r'') := by rw [hrep]; exact hV
  refine ⟨⟨L, r'', hm', hV'⟩, ?_⟩
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, hdeg σ σ' hσ, resDeg, resDeg, hq]
  have h4 : weilD Bw h (Loc.PP l) ρ σ = weilD Bw' h' (Loc.PP l) ρ σ' :=
    (weilD_apply Bw h (Loc.PP l) ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD (Loc.PP l) ρ g *
      ((phiU (Loc.PP l) ρ ^ (-m) : (Module.End ↥L.1 ↥(Dpst (Loc.PP l) ρ))ˣ) : Module.End ↥L.1 ↥(Dpst (Loc.PP l) ρ)))
      h1 h3).trans (weilD_apply Bw' h' (Loc.PP l) ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk (Loc.PP l) ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk (Loc.PP l) ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk (Loc.PP l) ι Bw' h' hj' ρ σ' x).symm)

private theorem hasLT_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : Plc F} {w : Plc K} (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) (c : Weil h' →* Weil h)
    (hc : ∀ σ', WeilRel (RingEquiv.refl Ω) (c σ') σ')
    (hs : ∀ f : Weil h →* ℂˣ, IsSmooth f → IsSmooth (f.comp c))
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ) (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ)
    (hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ = ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ)
    (H : Loc.HasLT h Bw hj ι wt a) : Loc.HasLT h' Bw' hj' ι wt' a' := by
  obtain ⟨μ, ξ, hμ, hξ, hP, h1, h2⟩ := H
  obtain ⟨t, ht, key, hr⟩ := exists_transfer h h' Bw Bw' hj hj' hK hJ hL hdeg hq ι
  obtain ⟨h3, h4⟩ := hr 1 _ hP
  refine ⟨μ.comp t, ξ.comp c, hμ.comp ht, hs ξ hξ, h3, fun σ' => ?_, fun σ' => ?_⟩
  · have e : t (Subgroup.inclusion (Weil_le_Dec h') σ') = Subgroup.inclusion (Weil_le_Dec h) (c σ') :=
      Subtype.ext (AlgEquiv.ext fun x => (key _ x).trans (hc σ' x).symm)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, h1, hp _ _ (hc σ')]
  · have e := h2 (c σ')
    rw [eig_of_wdRel h4 (hc σ')] at e
    exact e

private theorem cont_symm {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (i : v.adicCompletion F ≃+* w.adicCompletion K)
    (hi : Continuous i) : Continuous i.symm := by
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  exact (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i hi).1

end SlopeTestRemainingChoices

theorem UpperTheory.hasLocalLanglands_iff_of_placeIso :
    ∀ {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc K} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw'), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (jF : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) jF i → ∀ (ι : Qbar l ≃+* ℂ) (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ (τ : Emb l v) (τ' : Emb l w), τ.1 = τ'.1.comp i.toRingHom → wt τ = wt' τ') → ∀ (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ), (∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ)) → (UpperTheory.V.Loc.HasLT h Bw hj ι wt a ↔ UpperTheory.V.Loc.HasLT h' Bw' hj' ι wt' a') := by
  intro F K Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' O _ _ _ Bw Bw' hj hj' hK hJ hL jF i hP ι wt wt' hwt a a' ha
  obtain ⟨c, hc, hdeg, hq, hs⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have hi' : Continuous i.symm := cont_symm i hP.cont
  let E : Emb l w ≃ Emb l v :=
    { toFun := fun τ => ⟨τ.1.comp i.toRingHom, τ.2.comp hP.cont⟩
      invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.apply_symm_apply x))
      right_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.symm_apply_apply x)) }
  have hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ =
        ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ := by
    intro σ σ' hσ
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt (E τ) τ rfl, ha σ σ' hσ]
    rfl
  have sy : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ' σ → WeilRel (RingEquiv.refl Ω) σ σ' :=
    fun σ σ' H z => (H z).symm
  have hd : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ :=
    fun σ σ' H => by rw [← (hc σ σ').1 H, hdeg]
  refine ⟨hasLT_transfer h h' Bw Bw' hj hj' hK hJ hL hd hq ι c.symm.toMonoidHom
      (fun σ' => (hc _ _).2 (c.apply_symm_apply σ')) (fun f hf => (hs _ _).2 ?_) wt wt' a a' hp,
    hasLT_transfer h' h Bw' Bw hj' hj hK.symm hJ.symm hL.symm (fun σ' σ H => (hd σ σ' (sy _ _ H)).symm) hq.symm ι
      c.toMonoidHom (fun σ z => ((hc σ _).2 rfl z).symm) (fun f hf => (hs _ f).1 hf) wt' wt a' a
      fun σ' σ H => (hp σ σ' (sy _ _ H)).symm⟩
  have e : (f.comp c.symm.toMonoidHom).comp c.toMonoidHom = f :=
    MonoidHom.ext fun σ => congrArg f (c.symm_apply_apply σ)
  rw [e]
  exact hf
