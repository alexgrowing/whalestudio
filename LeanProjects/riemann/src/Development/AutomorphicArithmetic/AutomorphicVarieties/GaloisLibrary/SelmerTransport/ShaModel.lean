import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem resH1_injective_of_surjective {R G H M : Type} [CommRing R] [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) (π : H →* G) (hπ : Continuous π)
    (hs : Function.Surjective π) : Function.Injective (resH1 ρ π hπ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [LinearMap.mem_ker, resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    funext g
    obtain ⟨h, rfl⟩ := hs g
    have := congrFun hm h
    simpa [d0, restrictCocycles1] using this

private theorem resH1_bot_eq_zero {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) (x : H1 ρ) :
    resH1 ρ (⊥ : Subgroup G).subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resH1, Submodule.mapQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨0, ?_⟩
    funext u
    obtain ⟨u, hu⟩ := u
    rw [Subgroup.mem_bot] at hu
    subst hu
    have h1 := z.2.2 1 1
    simp at h1
    simp [d0, restrictCocycles1, h1]

private theorem resH1_eq_zero_of_le {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) {K L : Subgroup G} (h : K ≤ L) (x : H1 ρ)
    (hx : resH1 ρ L.subtype continuous_subtype_val x = 0) :
    resH1 ρ K.subtype continuous_subtype_val x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resH1, Submodule.mapQ_apply] at hx ⊢
    rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    funext u
    have := congrFun hm ⟨u.1, h u.2⟩
    simpa [d0, restrictCocycles1] using this

private theorem resU_resH1_subtype_eq {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) (x : H1 ρ) :
    resU ρ h (resH1 ρ U.subtype continuous_subtype_val x) = resH1 ρ U'.subtype continuous_subtype_val x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z', hz', hz'u⟩ := resU_mk ρ h (restrictCocycles1 ρ U.subtype continuous_subtype_val z)
    simp only [resH1, Submodule.mapQ_apply] at hz' ⊢
    rw [hz']
    congr 1
    ext u
    simp [hz'u, restrictCocycles1]
private theorem resH1_subtype_whole_bijective_sha {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (ρ : Representation R G M) :
    Function.Bijective (resH1 ρ (⊤ : Subgroup G).subtype continuous_subtype_val) := by
  refine ⟨resH1_injective_of_surjective ρ _ _ (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩), ?_⟩
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H z' =>
    have hz : (fun g : G => (z' : (⊤ : Subgroup G) → M) ⟨g, Subgroup.mem_top g⟩) ∈ Z1 ρ := by
      refine ⟨z'.2.1.comp (continuous_id.subtype_mk _), fun g h => ?_⟩
      exact z'.2.2 ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hz⟩, ?_⟩
    simp only [resH1, Submodule.mapQ_apply]
    congr 1

private theorem mem_shaAbs_iff_resH1_whole_mem_locSel {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[l] M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul ℤ_[l] M] (ρ : Representation ℤ_[l] (G E Ω) M)
    (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S = Above E l) (x : H1 ρ) :
    x ∈ LDataCardLeFinrank.ShaAbs ρ S ↔
      resH1 ρ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val x ∈ LocSel ρ ⊤ (shaFam E Ω l) := by
  subst hS
  have key : ∀ D : Subgroup (G E Ω),
      resU ρ (LocSel._proof_1 ⊤ D) (resH1 ρ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val x) = 0 ↔
        resH1 ρ D.subtype continuous_subtype_val x = 0 := by
    intro D
    rw [resU_resH1_subtype_eq]
    exact ⟨resH1_eq_zero_of_le ρ (le_inf le_top le_rfl) x, resH1_eq_zero_of_le ρ inf_le_right x⟩
  simp only [LDataCardLeFinrank.ShaAbs, LocSel, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, key]
  constructor
  · rintro ⟨h1, h2⟩ D hD
    rcases hD with ⟨A, hA, rfl⟩ | ⟨A, rfl⟩
    · have hA' : A ≠ ⊤ := fun h => ((places E Ω l A).2.1 h).2 hA
      obtain ⟨v, hv⟩ := (places E Ω l A).1 hA'
      exact h1 v (((places E Ω l A).2.2.1 v hv).1 hA) A hv
    · by_cases hT : A = ⊤
      · rw [((places E Ω l A).2.1 hT).1]
        exact resH1_bot_eq_zero ρ x
      · obtain ⟨v, hv⟩ := (places E Ω l A).1 hT
        by_cases hvS : v ∈ Above E l
        · exact resH1_eq_zero_of_le ρ (Ine_le_Dec A) x (h1 v hvS A hv)
        · exact h2 v hvS A hv
  · intro h
    refine ⟨fun v hv A hA => h _ (Or.inl ⟨A, ((places E Ω l A).2.2.1 v hA).2 hv, rfl⟩),
      fun v _ A _ => h _ (Or.inr ⟨A, rfl⟩)⟩
private theorem qzTw_comp_toGS_eq_qzG {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) = LDataCardLeFinrank.qzG E Ω l e := by
  have h1 : (D.chi ^ (-e)).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) = cycZ E Ω l ^ (-e) := by
    rw [← D.hchi]
    ext σ
    simp
  unfold qzTw LDataCardLeFinrank.qzG
  rw [← h1]
  rfl

private theorem qzTw_contAction {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) : ReciprocityTheory.Gal.ContAction (qzTw D e) := by
  have hq : Topology.IsQuotientMap
      (Prod.map (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) (id : QZ l → QZ l)) :=
    (IsOpenQuotientMap.prodMap ⟨QuotientGroup.mk_surjective, continuous_toGS Ω _, QuotientGroup.isOpenMap_coe⟩
      IsOpenQuotientMap.id).isQuotientMap
  unfold ReciprocityTheory.Gal.ContAction
  rw [hq.continuous_iff]
  have := LDataCardLeFinrank.contAction_qzG (F := E) (Ω := Ω) (l := l) e
  rw [← qzTw_comp_toGS_eq_qzG D e] at this
  exact this

private theorem sha_exists_cocycle_lift_whole {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) (ρ' : Representation ℤ_[l] (G E Ω) (QZ l))
    (hρ' : MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) = ρ')
    (𝒟 : Set (Subgroup (G E Ω))) (h𝒟 : shaFam E Ω l = 𝒟) :
    ∃ Ψ : Sha D e ≃ₗ[ℤ_[l]] LocSel ρ' ⊤ 𝒟, ∀ (x : Sha D e) (z : Z1 (qzTw D e)),
      x.1 = Submodule.Quotient.mk z → ∃ w : Z1U ρ' ⊤, (Ψ x).1 = Submodule.Quotient.mk w ∧
        ∀ σ : G E Ω, (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨σ, Subgroup.mem_top σ⟩ =
          (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω _ σ) := by
  subst hρ' h𝒟
  have hsurj : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩
  have hinj := resH1_injective_of_surjective (qzTw D e) _ (continuous_toGS Ω _) hsurj
  have hmapS := LDataCardLeFinrank.shaInfl E Ω D.S D.A D.hA ℤ_[l] (QZ l) (qzTw D e) (qzTw_contAction D e)
  have hbij := resH1_subtype_whole_bijective_sha (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))))
  have hEq : Submodule.map (resH1 _ (⊤ : Subgroup (G E Ω)).subtype continuous_subtype_val)
      (LDataCardLeFinrank.ShaAbs (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) (D.S : Set _)) =
      LocSel (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) ⊤ (shaFam E Ω l) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_shaAbs_iff_resH1_whole_mem_locSel l _ _ D.hS x).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨x, (mem_shaAbs_iff_resH1_whole_mem_locSel l _ _ D.hS x).2 hy, rfl⟩
  refine ⟨((Submodule.equivMapOfInjective _ hinj (Sha D e)).trans (LinearEquiv.ofEq _ _ hmapS)).trans
    (((LinearEquiv.ofBijective _ hbij).submoduleMap _).trans (LinearEquiv.ofEq _ _ hEq)), ?_⟩
  intro x z hz
  refine ⟨restrictCocycles1 _ _ continuous_subtype_val (restrictCocycles1 _ _ (continuous_toGS Ω _) z), ?_, fun σ => rfl⟩
  change (resH1 (MonoidHom.comp (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))) (⊤ : Subgroup (G E Ω)).subtype
      continuous_subtype_val) ((resH1 (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) (continuous_toGS Ω _)) x.1) = _
  rw [hz]
  rfl

theorem UpperTheory.V.Base.shaModel :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaU (LDataCardLeFinrank.qzG k Ω l e) l (galOf k E Ω), ∀ x, Infl k D e x.1 (Φ x).1 := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨_, hfam, _, hrep⟩ := galEmbFam k E Ω l
  obtain ⟨hemb, _, _⟩ := galEmbTop k E Ω
  have hmap : Subgroup.map (galEmb k E Ω) ⊤ = galOf k E Ω := by
    rw [← MonoidHom.range_eq_map, range_galEmb]
  obtain ⟨Φ, hΦ⟩ := selTransport ℤ_[l] (G k Ω) (QZ l) (LDataCardLeFinrank.qzG k Ω l e) (G E Ω) (galEmb k E Ω) hemb ⊤
    (galOf k E Ω) hmap (shaFam k Ω l)
  obtain ⟨Ψ, hΨ⟩ := sha_exists_cocycle_lift_whole D e (MonoidHom.comp (LDataCardLeFinrank.qzG k Ω l e) (galEmb k E Ω))
    ((qzTw_comp_toGS_eq_qzG D e).trans (hrep e).symm) _ hfam.symm
  have hr : ∀ u : galOf k E Ω, (u : G k Ω) ∈ Set.range (galEmb k E Ω) := fun u => by
    have hu : (u : G k Ω) ∈ (galEmb k E Ω).range := by
      rw [range_galEmb]
      exact u.2
    exact hu
  let ψ : galOf k E Ω → G E Ω := fun u => hemb.toHomeomorph.symm ⟨u.1, hr u⟩
  have hψc : Continuous ψ := hemb.toHomeomorph.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hψ : ∀ u, galEmb k E Ω (ψ u) = u := fun u =>
    congrArg Subtype.val (hemb.toHomeomorph.apply_symm_apply ⟨u.1, hr u⟩)
  have hψm : ∀ u v, ψ (u * v) = ψ u * ψ v := fun u v => hemb.injective (by rw [map_mul, hψ, hψ, hψ]; rfl)
  refine ⟨Ψ.trans Φ, fun x => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
  obtain ⟨w, hw1, hw2⟩ := hΨ x z hz.symm
  have hz'' : (fun u : galOf k E Ω => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ u, Subgroup.mem_top _⟩) ∈
      Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) := by
    refine ⟨w.2.1.comp (hψc.subtype_mk _), fun u v => ?_⟩
    have hw := w.2.2 ⟨ψ u, Subgroup.mem_top _⟩ ⟨ψ v, Subgroup.mem_top _⟩
    have e1 : (⟨ψ (u * v), Subgroup.mem_top _⟩ : (⊤ : Subgroup (G E Ω))) =
        ⟨ψ u, Subgroup.mem_top _⟩ * ⟨ψ v, Subgroup.mem_top _⟩ := Subtype.ext (hψm u v)
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hw ⊢
    rw [e1, hw, hψ]
  have hmem : Submodule.Quotient.mk w ∈ LocSel (MonoidHom.comp (LDataCardLeFinrank.qzG k Ω l e) (galEmb k E Ω)) ⊤
      (Subgroup.comap (galEmb k E Ω) '' shaFam k Ω l) := hw1 ▸ (Ψ x).2
  have hx : Ψ x = ⟨Submodule.Quotient.mk w, hmem⟩ := Subtype.ext hw1
  have hcomp := hΦ w ⟨_, hz''⟩ hmem (fun u' u hu => by
    obtain ⟨u', hu'⟩ := u'
    obtain ⟨u, hu2⟩ := u
    change (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ ⟨u, hu2⟩, Subgroup.mem_top _⟩ =
      (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨u', hu'⟩
    have h5 : ψ ⟨u, hu2⟩ = u' := by
      apply hemb.injective
      rw [hψ]
      exact hu.symm
    exact congrArg (fun s => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨s, Subgroup.mem_top s⟩) h5)
  refine ⟨z, ⟨_, hz''⟩, hz.symm, ?_, fun σ => ?_⟩
  · rw [LinearEquiv.trans_apply, hx, hcomp]
  · change (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨ψ ⟨galEmb k E Ω σ, _⟩, Subgroup.mem_top _⟩ = _
    rw [← hw2 σ]
    have h5 : ψ ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ = σ := hemb.injective (hψ _)
    exact congrArg (fun s => (w : (⊤ : Subgroup (G E Ω)) → QZ l) ⟨s, Subgroup.mem_top s⟩) h5
