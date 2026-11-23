import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTChartSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue GlobalTheory.Mean4O.CoverInt
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Points (PtsOver)

namespace GlobalTheory.Mean4O.CoverExc

theorem exists_etale_away (R A L : Type) [CommRing R] [CommRing A] [IsDomain A] [Field L] [Algebra R A] [Algebra A L]
    [Algebra R L] [IsScalarTower R A L] [IsFractionRing A L] [Algebra.FinitePresentation R A]
    [Algebra.FormallyEtale R L] :
    ∃ f : A, f ≠ 0 ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
      ((algebraMap A A').comp (algebraMap R A)).Etale := by
  have hl : IsLocalization.AtPrime L (⊥ : Ideal A) := by
    rw [IsLocalization.AtPrime, Ideal.primeCompl_bot]; infer_instance
  have e4 : Algebra.IsEtaleAt R (⊥ : Ideal A) :=
    .of_equiv ((IsLocalization.algEquiv (⊥ : Ideal A).primeCompl L
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars R)
  obtain ⟨b, hb, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal A)
  refine ⟨b, by simpa using hb, fun A' _ _ _ => ?_⟩
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  exact (Algebra.Etale.of_equiv ((IsLocalization.algEquiv (.powers b)
    (Localization.Away b) A').restrictScalars R) : Algebra.Etale R A')

section Model

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F} {j : G ⟶ X}

theorem exists_eq_app (H : IsPullback j q p (spMap (algebraMap (𝓞 F) F))) (W : G.Opens) (x : G) (hx : x ∈ W)
    {e : ℕ} (g : Fin e → Γ(G, W)) :
    ∃ (W' : X.Opens) (h : j ⁻¹ᵁ W' ≤ W), IsAffineOpen W' ∧ j x ∈ W' ∧ ∃ g' : Fin e → Γ(X, W'),
      ∀ a, (j.app W').hom (g' a) = resG G h (g a) := by
  obtain ⟨W₁, h₁, hx₁, n, g₁, hn, hg₁⟩ := GenericFibreInt.exists_nat_mul_eq_app F X G p q j H W x hx (Fin e) g
  have hunit (V : G.Opens) : IsUnit (n : Γ(G, V)) := by
    have : IsUnit (n : F) := (Nat.cast_ne_zero.2 hn).isUnit
    simpa using this.map (algX q V)
  have hb : j x ∈ X.basicOpen (n : Γ(X, W₁)) := by
    change x ∈ j ⁻¹ᵁ X.basicOpen (n : Γ(X, W₁))
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit G (hunit _)]
    exact hx₁
  obtain ⟨W', hW', hxW', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hb
  have hle₁ : W' ≤ W₁ := hle.trans (X.basicOpen_le _)
  have hu : IsUnit (n : Γ(X, W')) := by
    have h₀ : IsUnit (resG X (X.basicOpen_le (n : Γ(X, W₁))) n) := X.toRingedSpace.isUnit_res_basicOpen _
    simpa using h₀.map (resG X hle)
  obtain ⟨u, hu⟩ := hu
  refine ⟨W', (j.preimage_mono hle₁).trans h₁, hW', hxW', fun a => (u⁻¹ : _ˣ) * resG X hle₁ (g₁ a), fun a => ?_⟩
  refine (hunit _).mul_left_cancel ?_
  have e₁ : (n : Γ(G, j ⁻¹ᵁ W')) = (j.app W').hom u := by rw [hu, map_natCast]
  have e₂ := congrArg (resG G (j.preimage_mono hle₁)) (hg₁ a)
  rw [map_mul, map_natCast, GenericFibreInt.resG_resG'] at e₂
  rw [e₂, e₁, ← map_mul, Units.mul_inv_cancel_left, GenericFibreInt.app_resG']

theorem apply_genericPoint [IsIntegral X] [IsIntegral G] (H : IsPullback j q p (spMap (algebraMap (𝓞 F) F))) :
    j (genericPoint G) = genericPoint X := by
  have h : Flat (spMap (algebraMap (𝓞 F) F)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have : Flat j := MorphismProperty.of_isPullback (P := @Flat) H.flip h
  obtain ⟨y, -, hy⟩ := Flat.generalizingMap j (genericPoint_specializes (j (genericPoint G)))
  refine ((genericPoint_specializes _).antisymm ?_).eq.symm
  rw [← hy]
  exact (genericPoint_specializes y).map j.continuous

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem exists_etale_model [IsIntegral X] [IsIntegral G] [LocallyOfFiniteType p]
    (H : IsPullback j q p (spMap (algebraMap (𝓞 F) F))) {W : G.Opens} (hW : IsAffineOpen W)
    (hη : genericPoint G ∈ W) {e : ℕ} (g : Fin e → Γ(G, W)) (hg : (MvPolynomial.eval₂Hom (algX q W) g).Etale) :
    ∃ (W' : X.Opens) (h : j ⁻¹ᵁ W' ≤ W), IsAffineOpen W' ∧ genericPoint X ∈ W' ∧ ∃ g' : Fin e → Γ(X, W'),
      (MvPolynomial.eval₂Hom (algX p W') g').Etale ∧ ∀ a, (j.app W').hom (g' a) = resG G h (g a) := by
  obtain ⟨W₁, h₁, hW₁, hη₁, g₁, hg₁⟩ := exists_eq_app H W _ hη g
  have hj : IsPreimmersion j :=
    have h : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
    MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip h
  haveI : Nonempty W₁ := ⟨⟨_, hη₁⟩⟩
  have hbij : Function.Bijective (j.residueFieldMap (genericPoint G)).hom := by
    refine ⟨(j.residueFieldMap _).hom.injective, fun a => ?_⟩
    obtain ⟨b, rfl⟩ := G.residue_surjective _ a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective _ b
    refine ⟨X.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  let R := MvPolynomial (Fin e) (𝓞 F)
  let S := MvPolynomial (Fin e) F
  let L := G.residueField (genericPoint G)
  letI : Algebra R Γ(X, W₁) := (MvPolynomial.eval₂Hom (algX p W₁) g₁).toAlgebra
  letI : Algebra S Γ(G, W) := (MvPolynomial.eval₂Hom (algX q W) g).toAlgebra
  letI : Algebra Γ(G, W) L := (G.evaluation W _ hη).hom.toAlgebra
  letI := (X.evaluation W₁ _ hη₁).hom.toAlgebra
  letI : Algebra Γ(X, W₁) L := (X.evaluation W₁ _ hη₁ ≫ j.residueFieldMap _).hom.toAlgebra
  letI : Algebra S L := ((algebraMap Γ(G, W) L).comp (algebraMap S Γ(G, W))).toAlgebra
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower S Γ(G, W) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  have key (a : Γ(X, W₁)) (b : Γ(G, W)) (h : (j.app W₁).hom a = resG G h₁ b) :
      algebraMap Γ(X, W₁) L a = algebraMap Γ(G, W) L b := by
    change (X.evaluation W₁ _ hη₁ ≫ j.residueFieldMap _).hom a = _
    rw [Scheme.evaluation_naturality j _ hη₁, CommRingCat.hom_comp, RingHom.comp_apply, h]
    change (G.presheaf.map (homOfLE h₁).op ≫ G.evaluation _ _ hη₁).hom b = (G.evaluation W _ hη).hom b
    simp only [Scheme.evaluation]
    rw [← Category.assoc]
    exact congrArg (fun t => (t ≫ G.residue _).hom b) (G.presheaf.germ_res (homOfLE h₁) _ hη₁)
  haveI : IsScalarTower R Γ(X, W₁) L := by
    refine IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)
    · refine (key _ _ ?_).symm
      change (j.app W₁).hom (MvPolynomial.eval₂Hom (algX p W₁) g₁ (MvPolynomial.C a)) =
        resG G h₁ (MvPolynomial.eval₂Hom (algX q W) g (MvPolynomial.map (algebraMap _ _) (MvPolynomial.C a)))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, Scheme.Hom.app_eq_appLE]
      exact (RingHom.congr_fun (TopForm.appLE_comp_algX H.w le_rfl) a).trans
        (RingHom.congr_fun (TopForm.resG_comp_algX q h₁) _).symm
    · refine (key _ _ ?_).symm
      change (j.app W₁).hom (MvPolynomial.eval₂Hom (algX p W₁) g₁ (MvPolynomial.X a)) =
        resG G h₁ (MvPolynomial.eval₂Hom (algX q W) g (MvPolynomial.map (algebraMap _ _) (MvPolynomial.X a)))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hg₁]
  haveI := GenFiniteEtale.isFractionRing_eval G hW rfl hη
  haveI := GenFiniteEtale.isFractionRing_eval X hW₁ (apply_genericPoint H) hη₁
  haveI : IsFractionRing Γ(X, W₁) L := IsLocalization.isLocalization_of_algEquiv _
    ({ RingEquiv.ofBijective _ hbij with commutes' := fun _ => rfl } :
      X.residueField (j (genericPoint G)) ≃ₐ[Γ(X, W₁)] L)
  haveI : Algebra.Etale S Γ(G, W) := hg
  haveI : Algebra.FormallyEtale Γ(G, W) L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyEtale S L := .comp S Γ(G, W) L
  haveI : Algebra.FormallyEtale R S := .of_isLocalization ((nonZeroDivisors (𝓞 F)).map MvPolynomial.C)
  haveI : Algebra.FormallyEtale R L := .comp R S L
  have hft : (algX p W₁).FiniteType := by
    have h := HasRingHomProperty.appLE (@LocallyOfFiniteType) p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨W₁, hW₁⟩ le_top
    exact RingHom.finiteType_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).symm.commRingCatIsoToRingEquiv h
  have hft' : (algebraMap R Γ(X, W₁)).FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C) ?_
    convert hft using 1
    exact RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ a
  haveI : Algebra.FinitePresentation R Γ(X, W₁) :=
    Algebra.FinitePresentation.of_finiteType.1 (RingHom.finiteType_algebraMap.1 hft')
  obtain ⟨f, hf, hE⟩ := exists_etale_away R Γ(X, W₁) L
  haveI := hW₁.isLocalization_basicOpen f
  have hle := X.basicOpen_le f
  refine ⟨X.basicOpen f, (j.preimage_mono hle).trans h₁, hW₁.basicOpen f,
    GenFiniteEtale.genericPoint_mem_basicOpen hf, fun a => resG X hle (g₁ a), ?_, fun a => ?_⟩
  · convert hE Γ(X, X.basicOpen f) using 1
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · rw [MvPolynomial.eval₂Hom_C]
      exact (RingHom.congr_fun (TopForm.resG_comp_algX p hle) a).symm.trans
        (congrArg (resG X hle) (MvPolynomial.eval₂Hom_C _ g₁ a).symm)
    · rw [MvPolynomial.eval₂Hom_X']
      exact congrArg (resG X hle) (MvPolynomial.eval₂Hom_X' (algX p W₁) g₁ a).symm
  · rw [GenericFibreInt.app_resG', hg₁, GenericFibreInt.resG_resG']

end Model

section Fibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q)

include hπ in

theorem app_algX (U : X.Opens) (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
  have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
    rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
    (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
  simpa [Scheme.Hom.app_eq_appLE] using this.symm

include hπ in

theorem etale_app {U : X.Opens} {e : ℕ} {x : Fin e → Γ(X, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale)
    (het : (π.app U).hom.Etale) :
    (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)).Etale := by
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => (π.app U).hom (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [app_algX π hπ]
    · simp
  rw [hcx]
  exact RingHom.Etale.stableUnderComposition _ _ hx het

theorem encard_fibre [IsIntegral X] {σ : k →+* ℂ} {U : X.Opens} [Nonempty U] (hU : IsAffineOpen U)
    (hV : IsAffineOpen (π ⁻¹ᵁ U)) (hfin : (π.app U).hom.Finite) (het : (π.app U).hom.Etale) {y : CxPts p σ}
    (hy' : y ∈ ptsIn p σ U) :
    (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard =
      (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) : ℕ) := by
  set m := PtsOver.map π hπ (spMap σ) with hm
  have hmem (z : CxPts q σ) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := Iff.rfl
  rw [← EtaleFibre.encard_points_eq_finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) (π.app U).hom hfin het (evHom hy')]
  have hz (z : m ⁻¹' {y}) : z.1 ∈ ptsIn q σ (π ⁻¹ᵁ U) := (hmem z.1).2 (by rw [z.2]; exact hy')
  have hev (z : m ⁻¹' {y}) (a) : ev q σ _ ((π.app U).hom a) z.1 = ev p σ U a y := by
    exact (ev_app π hπ U a z.1).trans (congrArg _ z.2)
  refine Set.encard_congr (Equiv.ofBijective (fun z => ⟨evHom (hz z), RingHom.ext fun a => ?_⟩) ⟨?_, ?_⟩)
  · simp only [RingHom.comp_apply, ← ev_eq]
    exact hev z a
  · intro z z' h
    refine Subtype.ext (Subtype.ext (Points.ext_of_valR hV (hz z) (hz z') fun a => ?_))
    have := RingHom.congr_fun (congrArg Subtype.val h) a
    exact (ev_eq (hz z) a).trans (this.trans (ev_eq (hz z') a).symm)
  · rintro ⟨ψ, hψ⟩
    have hC (a : k) : ψ (algX q (π ⁻¹ᵁ U) a) = σ a := by
      rw [app_algX π hπ]
      exact (RingHom.congr_fun hψ _).trans ((ev_eq hy' _).symm.trans (ev_algX hy' a))
    have hzz := ofHom_mem hV ψ hC
    have hy₂ : m (ofHom hV ψ hC) = y := by
      refine Subtype.ext (Points.ext_of_valR hU hzz hy' fun a => ?_)
      exact ((ev_app π hπ U a _).symm.trans (ev_ofHom hV ψ hC _)).trans
        ((RingHom.congr_fun hψ a).trans (ev_eq hy' a).symm)
    refine ⟨⟨ofHom hV ψ hC, hy₂⟩, Subtype.ext (RingHom.ext fun a => ?_)⟩
    exact (ev_eq hzz a).symm.trans (ev_ofHom hV ψ hC a)

theorem etale_res {U₁ U : X.Opens} (hU₁ : IsAffineOpen U₁) (hU : IsAffineOpen U) (hle : U ≤ U₁) {e : ℕ}
    {x : Fin e → Γ(X, U₁)} (hx : (MvPolynomial.eval₂Hom (algX p U₁) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p U) fun a => resG X hle (x a)).Etale := by
  have hres : (resG X hle).Etale := by
    have := Scheme.Hom.etale_appLE (𝟙 X) hU₁ hU hle
    exact (Category.id_comp (X.presheaf.map (homOfLE hle).op) ▸ this :
      (X.presheaf.map (homOfLE hle).op).hom.Etale)
  have e : (MvPolynomial.eval₂Hom (algX p U) fun a => resG X hle (x a)) =
      (resG X hle).comp (MvPolynomial.eval₂Hom (algX p U₁) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simpa using (RingHom.congr_fun (TopForm.resG_comp_algX p hle) a).symm
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ hx hres

theorem exists_chart {σ : k →+* ℂ} {U : X.Opens} (hU : IsAffineOpen U) {e : ℕ} (x : Fin e → Γ(X, U))
    (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    ∃ c : AlgChart p σ e, y ∈ c.e.source ∧ c.e.source ⊆ ptsIn p σ U ∧
      ∀ w ∈ c.e.source, ∀ a, c.e w a = ev p σ U (x a) w := by
  obtain ⟨c, hc, rfl, hcx⟩ := AlgChart.exists_of_etale hU x hx hy
  obtain rfl : c.x = x := hcx
  exact ⟨c, hc, c.source_subset, c.apply_eq⟩

end Fibre

theorem exists_exceptional : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), Y.dim = e → V.IsDown I ε π → ∀ σ, ∃ T : Set (M.X (ε σ)), IsClosed T ∧ (∀ c : AlgChart Y.str (I.ε (ε σ)) e, MeasureTheory.volume ((tChart I c) '' ((tChart I c).source ∩ T)) = 0) ∧ (∀ c : AlgChart V.p σ e, MeasureTheory.volume (c.e '' (c.e.source ∩ π σ ⁻¹' T)) = 0) ∧ (∀ x ∉ T, (π σ ⁻¹' {x}).encard = V.deg) ∧ ∀ z, π σ z ∉ T → ∃ (c : AlgChart Y.str (I.ε (ε σ)) e) (c' : AlgChart V.p σ e), z ∈ c'.e.source ∧ I.pt _ (π σ z) ∈ c.e.source ∧ ∀ w ∈ c'.e.source, I.pt _ (π σ w) ∈ c.e.source → c'.e w = c.e (I.pt _ (π σ w)) := by
  intro F _ _ Y V e M I ε π he hD σ
  subst he
  obtain ⟨hσ, hD⟩ := hD σ
  choose l hl₁ hl₂ using hD
  set τ := I.ε (ε σ) with hτ
  have hg : V.π (genericPoint V.G) = genericPoint Y.X := by
    have h := (genericPoint_spec V.G).image V.π.continuous
    rw [Set.image_univ, V.π.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec Y.X)
  have hd : V.π.residueDegree (genericPoint V.G) ≠ 0 := V.deg_pos.ne'
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.str
  haveI : CharZero Γ(Y.X, ⊤) := charZero_of_injective_ringHom (algX Y.str ⊤).injective
  obtain ⟨U₁, x₁, hU₁, hg₁, hx₁⟩ := AlgChart.exists_etale_coords (p := Y.str) (D := Y.dim) (genericPoint Y.X)
  obtain ⟨U, hle, hU, hgU, hV, hfin, het, hr⟩ := GenFiniteEtale.exists_finite_etale_of_isProper V.π hg hd U₁ hg₁
  haveI : Nonempty U := ⟨⟨_, hgU⟩⟩
  let x : Fin Y.dim → Γ(Y.X, U) := fun a => resG Y.X hle (x₁ a)
  have hx : (MvPolynomial.eval₂Hom (algX Y.str U) x).Etale := etale_res hU₁ hU hle hx₁
  have hgV : genericPoint V.G ∈ V.π ⁻¹ᵁ U := show V.π (genericPoint V.G) ∈ U from hg ▸ hgU
  haveI := SchemeWords.isProper_of_isProjOver V.ar.isProjOver
  obtain ⟨W, hWle, hW, hgW, x', hx', hxx'⟩ := exists_etale_model V.pb hV hgV _ (etale_app V.π rfl hx het)
  have hgj := apply_genericPoint V.pb
  haveI := CoverHt.isPreimmersion_j V

  let U' : Y.X.Opens := ⟨(V.π '' (V.j ⁻¹ᵁ W : Set V.G)ᶜ)ᶜ,
    (V.π.isClosedMap _ (V.j ⁻¹ᵁ W).isOpen.isClosed_compl).isOpen_compl⟩
  have hU' (y : V.G) (hy : V.π y ∈ U') : V.j y ∈ W := not_not.1 fun h => hy ⟨y, h, rfl⟩
  have hgU' : genericPoint Y.X ∈ U' := by
    rintro ⟨y, hy, h⟩
    obtain rfl := GenFiniteEtale.eq_genericPoint V.π hg hd h
    exact hy (show V.j _ ∈ W from hgj ▸ hgW)
  obtain ⟨W₀, hW₀, hW₀e⟩ := V.j.isEmbedding.isInducing.isOpen_iff.1 (V.π ⁻¹ᵁ (U ⊓ U')).isOpen
  have hW₀' (y : V.G) : V.j y ∈ W₀ ↔ V.π y ∈ U ⊓ U' := Set.ext_iff.1 hW₀e y
  have hpt (z) : (I.pt _ (π σ z)).1 (IsLocalRing.closedPoint ℂ) = V.π (l z (IsLocalRing.closedPoint ℂ)) := by
    rw [← hl₂ z]
    exact Scheme.Hom.comp_apply _ _ _
  have hpt' (z : CxPts V.p σ) : z.1 (IsLocalRing.closedPoint ℂ) = V.j (l z (IsLocalRing.closedPoint ℂ)) := by
    rw [← hl₁ z]
    exact Scheme.Hom.comp_apply _ _ _
  have hs : spMap σ = spMap τ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Spec.map_comp, ← hσ]
    rfl
  refine ⟨I.pt _ ⁻¹' (ptsIn Y.str τ (U ⊓ U'))ᶜ, (isOpen_ptsIn _).isClosed_compl.preimage (I.pt _).continuous,
    fun c => ?_, fun c => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · refine measure_mono_null ?_ (GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str τ τ.injective (fun W hW => (algX Y.str W).injective)
      (U ⊓ U') ⟨hgU, hgU'⟩ _ c)
    rintro _ ⟨y, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨I.pt _ y, ⟨(mem_tChart_source I c).1 h₁, h₂⟩, rfl⟩
  · have hσi : Function.Injective σ := by
      rw [← hσ]
      exact τ.injective.comp (IsFractionRing.injective (𝓞 F) F)
    have hinj (W : V.X.Opens) (hW : Nonempty W) : Function.Injective (algX V.p W) := by
      obtain ⟨⟨y, hy⟩⟩ := hW
      have hη : genericPoint V.G ∈ V.j ⁻¹ᵁ W :=
        show V.j _ ∈ W from hgj ▸ (genericPoint_specializes y).mem_open W.isOpen hy
      haveI : Nonempty (V.j ⁻¹ᵁ W) := ⟨⟨_, hη⟩⟩
      refine Function.Injective.of_comp (f := (V.j.appLE W _ le_rfl).hom) ?_
      rw [← RingHom.coe_comp, TopForm.appLE_comp_algX V.pb.w, RingHom.coe_comp]
      exact (algX (V.π ≫ Y.str) _).injective.comp (IsFractionRing.injective (𝓞 F) F)
    refine measure_mono_null ?_ (GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn (𝓞 F) V.X V.p σ hσi hinj ⟨W₀, hW₀⟩ ?_ _ c)
    · refine Set.image_mono (Set.inter_subset_inter_right _ fun z hz hz' => hz ?_)
      rw [mem_ptsIn, hpt, ← hW₀', ← hpt']
      exact mem_ptsIn.1 hz'
    · change genericPoint V.X ∈ W₀
      rw [← hgj, hW₀', hg]
      exact ⟨hgU, hgU'⟩
  · have hy' : I.pt _ y ∈ ptsIn Y.str τ U := ptsIn_mono inf_le_left (not_not.1 hy)
    have hc := encard_fibre V.π rfl hU hV hfin het hy'
    rw [hr] at hc
    refine Eq.trans ?_ hc
    refine Set.encard_congr (Equiv.ofBijective (fun z => ⟨⟨l z.1, by rw [← Category.assoc, hl₂]; exact (I.pt _ _).2⟩,
      Subtype.ext ((hl₂ _).trans (by rw [z.2]))⟩) ⟨fun z z' h => ?_, ?_⟩)
    · have h' : l z.1 = l z'.1 := congrArg (fun t => t.1.1) h
      exact Subtype.ext (Subtype.ext (by rw [← hl₁, ← hl₁, h']))
    · rintro ⟨⟨w, hw⟩, hw'⟩
      let z : CxPts V.p σ := ⟨w ≫ V.j, by rw [Category.assoc, V.pb.w, ← Category.assoc, hw, hs]⟩
      have hz : l z = w := (cancel_mono V.j).1 (hl₁ z)
      refine ⟨⟨z, (I.pt _).injective (Subtype.ext ?_)⟩, Subtype.ext (Subtype.ext hz)⟩
      rw [← hl₂, hz]
      exact congrArg Subtype.val hw'
  · have hz' : I.pt _ (π σ z) ∈ ptsIn Y.str τ (U ⊓ U') := not_not.1 hz
    have hzW : z ∈ ptsIn V.p σ W := by
      rw [mem_ptsIn, hpt']
      exact hU' _ (hpt z ▸ (mem_ptsIn.1 hz').2)
    obtain ⟨c, hc, -, hcx⟩ := exists_chart hU x hx (ptsIn_mono inf_le_left hz')
    obtain ⟨c', hc', hs', hcx'⟩ := exists_chart hW x' hx' hzW
    refine ⟨c, c', hc', hc, fun w hw hw' => ?_⟩
    ext a
    have hwW : ⊤ ≤ l w ⁻¹ᵁ V.j ⁻¹ᵁ W := by
      have := hs' hw
      rw [ptsIn, Set.mem_setOf_eq, ← hl₁] at this
      exact this
    rw [hcx' w hw a, hcx _ hw' a, ev, ev, ← hl₁, ← hl₂, Points.valR_comp, Points.valR_comp, hxx']
    exact Points.valR_res _ _ hwW _

end GlobalTheory.Mean4O.CoverExc
