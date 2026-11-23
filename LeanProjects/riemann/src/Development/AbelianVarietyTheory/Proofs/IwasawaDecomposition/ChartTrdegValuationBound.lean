import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapResMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.FlagGen

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ValSpec
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {φ ψ : A →+* B} (h : spMap φ = spMap ψ) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_apply {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (q : Sp B) :
    spMap φ q = PrimeSpectrum.comap φ q := rfl

theorem universallyClosed_π (Z : Mdl Y i₀) : UniversallyClosed Z.π := by
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsProper Z.s := inferInstanceAs (IsProper (_ ≫ _))
  have : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  have : IsProper (Z.π ≫ (Y Z.i).s) := by rw [Z.π_s]; infer_instance
  have := IsProper.of_comp Z.π (Y Z.i).s
  infer_instance

theorem exists_lift (Z : Mdl Y i₀) {Ω : Type} [Field Ω] (R : ValuationSubring Ω) (w : Sp Ω ⟶ Z.X)
    (y : Sp R ⟶ (Y Z.i).X) (h : w ≫ Z.π = spMap R.subtype ≫ y) :
    ∃ V : Sp R ⟶ Z.X, spMap R.subtype ≫ V = w ∧ V ≫ Z.π = y := by
  have := universallyClosed_π Z
  have hv : (ValuativeCriterion.Existence ⊓ @QuasiCompact) Z.π := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, h₁, h₂⟩⟩ := hv.1 ⟨R, Ω, w, y, ⟨h⟩⟩
  exact ⟨l, h₁, h₂⟩

theorem exists_chart_fac_local (Z : Mdl Y i₀) {R : Type} [CommRing R] [IsLocalRing R] (V : Sp R ⟶ Z.X) (a : Fin Z.m)
    (h : V (IsLocalRing.closedPoint R) ∈ ((Z.U a).1 : Set Z.X)) :
    ∃ ρ : Γ(Z.X, (Z.U a).1) →+* R, spMap ρ ≫ Z.chart a = V := by
  refine Z.exists_chart_fac V a ?_
  rintro _ ⟨q, rfl⟩
  have hs : q ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes q (IsLocalRing.closedPoint R)).1 (IsLocalRing.le_maximalIdeal q.2.ne_top)
  exact (hs.map V.continuous).mem_open (Z.U a).1.2 h

theorem exists_residue_fac {A : Type} [CommRing A] (x : Sp A) {Ω : Type} [Field Ω] (φ : A →+* Ω)
    (h : spMap φ (IsLocalRing.closedPoint Ω) = x) : ∃ σ : (Sp A).residueField x →+* Ω, σ.comp (resMap x) = φ := by
  subst h
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω (Sp A) (spMap φ)
  refine ⟨(Scheme.descResidueField (Scheme.stalkClosedPointTo (spMap φ))).hom, spMap_inj ?_⟩
  rw [← spMap_comp', spMap_resMap]
  exact e

theorem spMap_comp_resMap_apply {A : Type} [CommRing A] (x : Sp A) {T : Type} [CommRing T]
    (τ : (Sp A).residueField x →+* T) (q : Sp T) : spMap (τ.comp (resMap x)) q = x := by
  rw [← spMap_comp', spMap_resMap, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem residueFieldMap_eq {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : Sp A) {Ω : Type} [Field Ω]
    (σ τ : (Sp A).residueField x →+* Ω) (h : spMap (σ.comp (resMap x)) ≫ f = spMap (τ.comp (resMap x)) ≫ f) :
    σ.comp (f.residueFieldMap x).hom = τ.comp (f.residueFieldMap x).hom := by
  apply spMap_inj
  rw [← spMap_comp', ← spMap_comp', spMap_resMap] at h
  simp only [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h
  have h' : spMap σ ≫ Spec.map (f.residueFieldMap x) = spMap τ ≫ Spec.map (f.residueFieldMap x) :=
    (cancel_mono (X.fromSpecResidueField (f x))).1 (by simpa only [Category.assoc] using h)
  rw [← spMap_comp', ← spMap_comp']
  exact h'

theorem alg_eq_of_π (Z : Mdl Y i₀) {S : Type} [CommRing S] {a₁ a₂ : Fin Z.m} {φ₁ : Γ(Z.X, (Z.U a₁).1) →+* S}
    {φ₂ : Γ(Z.X, (Z.U a₂).1) →+* S} (h : spMap φ₁ ≫ Z.chart a₁ ≫ Z.π = spMap φ₂ ≫ Z.chart a₂ ≫ Z.π) :
    φ₁.comp (Z.alg a₁) = φ₂.comp (Z.alg a₂) :=
  coeff_ext (W := W) (by rw [← Z.affineOpenChart_comp_structure_eq_spMap, ← Z.affineOpenChart_comp_structure_eq_spMap, ← Z.π_s, reassoc_of% h])

theorem chart_lift (Z : Mdl Y i₀) (a : Fin Z.m) : ∃ g : Sp Γ(Z.X, (Z.U a).1) ⟶ (Xo Z.i.l).XF Z.i.c,
    g ≫ (Y Z.i).j = Z.chart a ≫ Z.π ∧ g ≫ pullback.snd _ _ = spMap (Z.alg a) := by
  have hj := GlobalTheory.TriplesAlong.isOpenImmersion_j W (Y Z.i)
  have hr : Set.range (Z.chart a ≫ Z.π) ⊆ Set.range (Y Z.i).j := by
    rintro _ ⟨x, rfl⟩
    have hx : Z.chart a x ∈ Z.toPre.opn := by
      rw [← Z.cover]
      refine Set.mem_iUnion.2 ⟨a, ?_⟩
      have : Set.range (Z.chart a) = ((Z.U a).1 : Set Z.X) := (Z.U a).2.range_fromSpec
      rw [← this]
      exact ⟨x, rfl⟩
    simpa [Pre.opn, Scheme.Hom.comp_apply] using hx
  refine ⟨IsOpenImmersion.lift (Y Z.i).j (Z.chart a ≫ Z.π) hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have := mono_spMap_subtype (Z.i.c.V W)
  rw [← cancel_mono (spMap (Z.i.c.V W).subtype), Category.assoc, ← GlobalTheory.LocM.BaseMdl.j_s, ← Category.assoc,
    IsOpenImmersion.lift_fac, Category.assoc, Z.π_s, Z.alg_s]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem flag_gen (Z : Mdl Y i₀) {Ω : Type} [Field Ω] {w : Sp Ω ⟶ Z.X} {u : Vecs Dw (Y Z.i).t Ω} (hF : Z.FlagAt w u)
    (a₁ : Fin Z.m) (φ₁ : Γ(Z.X, (Z.U a₁).1) →+* Ω) (e : spMap φ₁ ≫ Z.chart a₁ = w) :
    SameFlag Z.ty (Y Z.i).t (spMap φ₁ ≫ Z.chart a₁ ≫ Z.π) ((Z.fr a₁).bc φ₁) u := by
  obtain ⟨a₂, φ₂, e₂, -, hs⟩ := hF
  have h12 : spMap φ₁ ≫ Z.chart a₁ = spMap φ₂ ≫ Z.chart a₂ := e.trans e₂.symm
  have hg := Z.glue Ω a₁ a₂ φ₁ φ₂ h12
  have hx : w ≫ Z.π = spMap φ₁ ≫ Z.chart a₁ ≫ Z.π := by rw [← e, Category.assoc]
  rw [hx] at hs
  have F₁ := GlobalTheory.LocM.Diag.frame_at Z a₁ φ₁
  have F₂ := GlobalTheory.LocM.Diag.frame_at Z a₂ φ₂
  rw [← Z.alg_eq h12, ← reassoc_of% h12] at F₂
  exact SameFlag.trans (fun τ i => (F₁.1 τ i).1) (fun τ i => (F₁.exists_comb F₂ τ i).exists) hg hs

end GlobalTheory.ValSpec

set_option maxHeartbeats 1000000 in
open GlobalTheory.ValSpec in

theorem GlobalTheory.FlagGen.exists_embedding_of_specialisation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀) (a : Fin Z.m) (x : Sp Γ(Z.X, (Z.U a).1)),
    (∀ x' : Sp Γ(Z.X, (Z.U a).1), (Z.chart a ≫ Z.π) x' = (Z.chart a ≫ Z.π) x → x' ⤳ x → x' = x) →
    ∀ (Ω : Type) [Field Ω] (R : ValuationSubring Ω) (ι : (Sp Γ(Z.X, (Z.U a).1)).residueField x →+* R)
      (v : Vecs Dw (Y Z.i).t R),
    GlobalTheory.LocM.IsFrame (Y Z.i).t ((ι.comp (resMap x)).comp (Z.alg a)) (spMap (ι.comp (resMap x)) ≫ Z.chart a ≫ Z.π) v →
    GlobalTheory.LocM.SameFlag Z.ty (Y Z.i).t (spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ Z.chart a ≫ Z.π)
      ((Z.fr a).bc ((IsLocalRing.residue R).comp (ι.comp (resMap x)))) (v.bc (IsLocalRing.residue R)) →
    ∃ σ : (Sp Γ(Z.X, (Z.U a).1)).residueField x →+* Ω,
      σ.comp ((Z.chart a ≫ Z.π).residueFieldMap x).hom = (R.subtype.comp ι).comp ((Z.chart a ≫ Z.π).residueFieldMap x).hom ∧
      σ.comp ((resMap x).comp (Z.alg a)) = (R.subtype.comp ι).comp ((resMap x).comp (Z.alg a)) ∧
      GlobalTheory.LocM.SameFlag Z.ty (Y Z.i).t (spMap ((R.subtype.comp ι).comp (resMap x)) ≫ Z.chart a ≫ Z.π)
        ((Z.fr a).bc (σ.comp (resMap x))) (v.bc R.subtype) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z a x hgen Ω _ R ι v hv hflag
  obtain ⟨g, hgj, hgs⟩ := chart_lift Z a

  have Fv := GlobalTheory.LocM.isFrame_bc _ _ _ _ _ _ _ _ _ _ R.subtype _ _ hv
  obtain ⟨wΩ, ⟨hwπ, hwF⟩, -⟩ := Z.bij Ω _ (spMap (R.subtype.comp (ι.comp (resMap x))) ≫ g)
    (by rw [Category.assoc, hgs, spMap_comp']) (v.bc R.subtype)
    (by rw [Category.assoc, hgj, ← spMap_comp' (ι.comp (resMap x)) R.subtype, Category.assoc]; exact Fv)

  obtain ⟨V, hV, hVπ⟩ := exists_lift Z R wΩ (spMap (ι.comp (resMap x)) ≫ Z.chart a ≫ Z.π)
    (by rw [hwπ, Category.assoc, hgj, ← spMap_comp' (ι.comp (resMap x)) R.subtype, Category.assoc])

  have hc : V (IsLocalRing.closedPoint R) ∈ Z.toPre.opn := by
    show Z.π (V _) ∈ Set.range (Y Z.i).j
    have e3 : Z.π (V (IsLocalRing.closedPoint R)) = (V ≫ Z.π) (IsLocalRing.closedPoint R) := rfl
    rw [e3, hVπ, ← hgj]
    exact ⟨(spMap (ι.comp (resMap x)) ≫ g) (IsLocalRing.closedPoint R), rfl⟩
  rw [← Z.cover] at hc
  obtain ⟨a', ha'⟩ := Set.mem_iUnion.1 hc
  obtain ⟨ρ', hρ'⟩ := exists_chart_fac_local Z V a' ha'
  have hco' : ρ'.comp (Z.alg a') = (ι.comp (resMap x)).comp (Z.alg a) := alg_eq_of_π Z (by rw [reassoc_of% hρ', hVπ])

  have hR : SameFlag Z.ty (Y Z.i).t (spMap ρ' ≫ Z.chart a' ≫ Z.π) ((Z.fr a').bc ρ') v := by
    have F' := GlobalTheory.LocM.Diag.frame_at Z a' ρ'
    have hv' : IsFrame (Y Z.i).t (ρ'.comp (Z.alg a')) (spMap ρ' ≫ Z.chart a' ≫ Z.π) v := by
      rw [hco', reassoc_of% hρ', hVπ]; exact hv
    refine GlobalTheory.DRFlag.Spez.sameFlag_of_bc (φ := R.subtype) Subtype.val_injective F' hv' ?_
    rw [Vecs.bc_bc, ← Category.assoc, spMap_comp' ρ' R.subtype]
    exact flag_gen Z hwF a' (R.subtype.comp ρ') (by rw [← spMap_comp' ρ' R.subtype, Category.assoc, hρ', hV])

  have hres := GlobalTheory.DRFlag.Spez.sameFlag_bc (IsLocalRing.residue R) hR
  rw [Vecs.bc_bc, ← Category.assoc, spMap_comp' ρ' (IsLocalRing.residue R)] at hres
  have hP : spMap ((IsLocalRing.residue R).comp ρ') ≫ Z.chart a' ≫ Z.π =
      spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ Z.chart a ≫ Z.π := by
    rw [← spMap_comp' ρ' (IsLocalRing.residue R), ← spMap_comp' (ι.comp (resMap x)) (IsLocalRing.residue R)]
    simp only [Category.assoc]
    rw [reassoc_of% hρ', hVπ]
  rw [hP] at hres
  have F0 := GlobalTheory.LocM.Diag.frame_at Z a ((IsLocalRing.residue R).comp (ι.comp (resMap x)))
  have Fvr := GlobalTheory.LocM.isFrame_bc _ _ _ _ _ _ _ _ _ _ (IsLocalRing.residue R) _ _ hv
  rw [← Category.assoc, spMap_comp' (ι.comp (resMap x)) (IsLocalRing.residue R)] at Fvr
  have Fa' := GlobalTheory.LocM.Diag.frame_at Z a' ((IsLocalRing.residue R).comp ρ')
  rw [hP] at Fa'
  have hsym := GlobalTheory.LocM.MapComp.sameFlag_symm (fun τ i => (F0.1 τ i).1) Fvr hflag
  have htr := GlobalTheory.LocM.MapComp.sameFlag_trans (fun τ i => (Fa'.1 τ i).1) (fun τ i => (Fvr.1 τ i).1)
    (fun τ i => (F0.1 τ i).1) hres hsym

  obtain ⟨w₀, -, huniq⟩ := Z.bij (IsLocalRing.ResidueField R) _
    (spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ g) (by rw [Category.assoc, hgs, spMap_comp'])
    ((Z.fr a).bc ((IsLocalRing.residue R).comp (ι.comp (resMap x)))) (by rw [Category.assoc, hgj]; exact F0)
  have e1 := huniq (spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ Z.chart a)
    ⟨by rw [Category.assoc, Category.assoc, hgj], GlobalTheory.LocM.Diag.flagAt_chart Z a _⟩
  have e2 := huniq (spMap ((IsLocalRing.residue R).comp ρ') ≫ Z.chart a')
    ⟨by rw [Category.assoc, hP, Category.assoc, hgj],
      ⟨a', (IsLocalRing.residue R).comp ρ', rfl, by rw [Category.assoc, hP, RingHom.comp_assoc, hco']; exact F0,
        by rw [Category.assoc, hP]; exact htr⟩⟩
  have hw := e2.trans e1.symm
  have h3 : spMap (IsLocalRing.residue R) ≫ V = spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) ≫ Z.chart a := by
    rw [← hρ', ← Category.assoc, spMap_comp' ρ' (IsLocalRing.residue R), hw]
  have hcl : ∀ q : Sp (IsLocalRing.ResidueField R), spMap (IsLocalRing.residue R) q = IsLocalRing.closedPoint R := by
    intro q
    have : Subsingleton (Sp (IsLocalRing.ResidueField R)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (IsLocalRing.ResidueField R)))
    rw [spMap_apply, Subsingleton.elim q (IsLocalRing.closedPoint _)]
    exact IsLocalRing.comap_closedPoint _
  let q₀ : Sp (IsLocalRing.ResidueField R) := IsLocalRing.closedPoint _
  have hVa : V (IsLocalRing.closedPoint R) ∈ ((Z.U a).1 : Set Z.X) := by
    rw [← hcl q₀, ← Scheme.Hom.comp_apply, h3, Scheme.Hom.comp_apply, ← (Z.U a).2.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ := exists_chart_fac_local Z V a hVa
  have hco : ρ.comp (Z.alg a) = (ι.comp (resMap x)).comp (Z.alg a) := alg_eq_of_π Z (by rw [reassoc_of% hρ, hVπ])

  have e : spMap (R.subtype.comp ρ) ≫ Z.chart a ≫ Z.π =
      spMap ((R.subtype.comp ι).comp (resMap x)) ≫ Z.chart a ≫ Z.π := by
    rw [← spMap_comp' ρ R.subtype, Category.assoc, reassoc_of% hρ, hVπ, ← Category.assoc,
      spMap_comp' (ι.comp (resMap x)) R.subtype]
  let qΩ : Sp Ω := IsLocalRing.closedPoint Ω
  have hx'π : (Z.chart a ≫ Z.π) (spMap (R.subtype.comp ρ) qΩ) = (Z.chart a ≫ Z.π) x := by
    have := congrArg (fun m => m qΩ) e
    simp only [Scheme.Hom.comp_apply] at this ⊢
    rw [this, spMap_comp_resMap_apply]
  have h4 : spMap ((IsLocalRing.residue R).comp ρ) = spMap ((IsLocalRing.residue R).comp (ι.comp (resMap x))) := by
    have := (Z.U a).2.isOpenImmersion_fromSpec
    refine (cancel_mono ((Z.U a).2.fromSpec)).1 ?_
    show _ ≫ Z.chart a = _ ≫ Z.chart a
    rw [← spMap_comp' ρ (IsLocalRing.residue R), Category.assoc, hρ, h3]
  have hx'sp : spMap (R.subtype.comp ρ) qΩ ⤳ x := by
    have e0 : spMap (R.subtype.comp ρ) qΩ = spMap ρ (spMap R.subtype qΩ) := by
      rw [← spMap_comp' ρ R.subtype, Scheme.Hom.comp_apply]
    have h1 : spMap R.subtype qΩ ⤳ IsLocalRing.closedPoint R :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (spMap R.subtype qΩ).2.ne_top)
    have h2 : spMap ρ (IsLocalRing.closedPoint R) = x := by
      rw [← hcl q₀, ← Scheme.Hom.comp_apply, spMap_comp' ρ (IsLocalRing.residue R), h4]
      exact spMap_comp_resMap_apply x ((IsLocalRing.residue R).comp ι) q₀
    rw [e0, ← h2]
    exact h1.map (spMap ρ).continuous
  have hx' := hgen _ hx'π hx'sp
  obtain ⟨σ, hσ⟩ := exists_residue_fac x (R.subtype.comp ρ) hx'
  refine ⟨σ, ?_, ?_, ?_⟩
  · apply residueFieldMap_eq
    rw [hσ]
    exact e
  · show (σ.comp (resMap x)).comp (Z.alg a) = ((R.subtype.comp ι).comp (resMap x)).comp (Z.alg a)
    rw [hσ, RingHom.comp_assoc, hco]
    rfl
  · rw [hσ, ← e]
    exact flag_gen Z hwF a (R.subtype.comp ρ) (by rw [← spMap_comp' ρ R.subtype, Category.assoc, hρ, hV])
