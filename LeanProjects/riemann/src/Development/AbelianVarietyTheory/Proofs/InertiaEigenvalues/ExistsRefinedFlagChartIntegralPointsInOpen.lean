import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AdjoinRatiosOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.GoodRefine

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_lift {X : Scheme.{0}} {C A : Type} [CommRing C] [CommRing A] (ι : Sp C ⟶ X) [IsOpenImmersion ι]
    (f : Sp A ⟶ X) (h : Set.range f ⊆ Set.range ι) : ∃ φ : C →+* A, spMap φ ≫ ι = f := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ι f h)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift ι f h)).hom = IsOpenImmersion.lift ι f h :=
    Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem exists_gens {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {S : Set X} (hS : IsOpen S) {R V F : Type} [CommRing R] [CommRing V] [IsLocalRing V] [Field F]
    (w : Sp R ⟶ X) (b : O →+* R) (hb : w ≫ s = spMap b) (a : V →+* F) (ψ : R →+* F) (y' : Sp V ⟶ X)
    (hy : spMap ψ ≫ w = spMap a ≫ y') (hr : Set.range y' ⊆ S) :
    ∃ g : R, ψ g ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), IsUnit (i g) → ∃ cs : Finset R',
      (∀ ψ' : R' →+* F, ψ'.comp i = ψ → ∀ x ∈ cs, ψ' x ∈ a.range) ∧
      ∀ (V₁ F₁ : Type) [CommRing V₁] [CommRing F₁] (a₁ : V₁ →+* F₁), Function.Injective a₁ →
        ∀ ψ₁ : R' →+* F₁, (∀ o, ψ₁ (i (b o)) ∈ a₁.range) → (∀ x ∈ cs, ψ₁ x ∈ a₁.range) →
        ∃ y₁ : Sp V₁ ⟶ X, spMap (ψ₁.comp i) ≫ w = spMap a₁ ≫ y₁ ∧ Set.range y₁ ⊆ S := by
  classical
  obtain ⟨C, ι, hι, hmem, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X) (x := y' (IsLocalRing.closedPoint V)) (U := ⟨S, hS⟩) (hr ⟨_, rfl⟩)
  change Sp C ⟶ X at ι
  have hry : Set.range y' ⊆ Set.range ι := by
    have htop : y' ⁻¹ᵁ ι.opensRange = ⊤ := (IsLocalRing.closedPoint_mem_iff (y' ⁻¹ᵁ ι.opensRange)).1 hmem
    rintro _ ⟨p, rfl⟩
    have : p ∈ y' ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
    exact this
  obtain ⟨γ, hγ⟩ := exists_lift ι y' hry
  obtain ⟨β, hβ⟩ : ∃ β : O →+* C, spMap β = ι ≫ s := ⟨(Spec.preimage (ι ≫ s)).hom, Spec.map_preimage _⟩
  have hft : β.FiniteType := by
    have : LocallyOfFiniteType (spMap β) := by rw [hβ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  letI := β.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O C from hft).out
  let p₀ : Sp F := (⊥ : PrimeSpectrum F)
  have hp : spMap ψ p₀ ∈ w ⁻¹ᵁ ι.opensRange := by
    apply hry
    refine ⟨spMap a p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hy, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨g, rfl⟩, hg1, hg2⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (spMap ψ p₀ : PrimeSpectrum R) ∈ ((w ⁻¹ᵁ ι.opensRange : (Sp R).Opens) : Set (Sp R)) from hp)
    (w ⁻¹ᵁ ι.opensRange).isOpen
  refine ⟨g, fun h0 => hg1 (show ψ g ∈ (⊥ : Ideal F) from h0), fun R' _ i hu => ?_⟩
  have hri : Set.range (spMap i ≫ w) ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hg2
    intro hm
    exact (show PrimeSpectrum R' from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  obtain ⟨φ, hφ⟩ := exists_lift ι _ hri
  have hφβ : φ.comp β = i.comp b := by
    apply sp_inj
    rw [← sp_comp, ← sp_comp, hβ, ← hb, ← Category.assoc, hφ, Category.assoc]
  refine ⟨t.image φ, fun ψ' hψ x hx => ?_, fun V₁ F₁ _ _ a₁ ha ψ₁ h1 h2 => ?_⟩
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    have : ψ'.comp φ = a.comp γ := by
      apply sp_inj
      rw [← cancel_mono ι, ← sp_comp, ← sp_comp, Category.assoc, Category.assoc, hφ, hγ, ← hy, ← hψ, ← sp_comp,
        Category.assoc]
    exact ⟨γ u, (DFunLike.congr_fun this u).symm⟩
  · have hall : ∀ u : C, (ψ₁.comp φ) u ∈ a₁.range := by
      intro u
      have hu : u ∈ Algebra.adjoin O (t : Set C) := by rw [ht]; trivial
      induction hu using Algebra.adjoin_induction with
      | mem x hx => exact h2 _ (Finset.mem_image_of_mem _ hx)
      | algebraMap r =>
        have := DFunLike.congr_fun hφβ r
        change ψ₁ ((φ.comp β) r) ∈ _
        rw [this]; exact h1 r
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    let eq := RingEquiv.ofBijective a₁.rangeRestrict ⟨fun x y h => ha (congrArg Subtype.val h), a₁.rangeRestrict_surjective⟩
    let γ₁ : C →+* V₁ := eq.symm.toRingHom.comp ((ψ₁.comp φ).codRestrict a₁.range hall)
    have hγ₁ : a₁.comp γ₁ = ψ₁.comp φ := by
      ext u
      exact congrArg Subtype.val (eq.apply_symm_apply ((ψ₁.comp φ).codRestrict a₁.range hall u))
    refine ⟨spMap γ₁ ≫ ι, ?_, ?_⟩
    · rw [← Category.assoc, sp_comp, hγ₁, ← sp_comp, ← sp_comp, Category.assoc, Category.assoc, hφ]
    · rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hsub ⟨_, rfl⟩

theorem exists_invert {K Ω L V : Type} [Field K] [Field Ω] [Field L] [Algebra K Ω] [Algebra K L] [CommRing V]
    [IsDomain V] [ValuationRing V] [Algebra V L] [IsFractionRing V L] (R : Subalgebra K Ω) (g : R) (ψ : R →ₐ[K] L)
    (hg : ψ g ≠ 0) :
    ∃ (R₀ : Subalgebra K Ω) (hle : R ≤ R₀) (ψ₀ : R₀ →ₐ[K] L) (h : R₀), (g : Ω) ≠ 0 ∧ (g : Ω)⁻¹ ∈ R₀ ∧
      (Algebra.Smooth K R → Algebra.Smooth K R₀) ∧ ψ₀.comp (Subalgebra.inclusion hle) = ψ ∧ (h : Ω) ≠ 0 ∧
      (h : Ω)⁻¹ ∈ R₀ ∧ ψ₀ h ∈ (algebraMap V L).range ∧
      ∀ R' : Subalgebra K Ω, R ≤ R' → (h : Ω) ∈ R' → (h : Ω)⁻¹ ∈ R' → R₀ ≤ R' := by
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by rw [show g = 0 from Subtype.ext h0, map_zero])
  obtain ⟨hle, hinv, hsm, hext⟩ := GlobalTheory.adjoin_ratios_of_span_eq_top K Ω R 2 ![1, g] 1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one) hg0 _ rfl
  obtain ⟨ψ₀, hc, hr⟩ := hext L ψ hg
  have hmin : ∀ R' : Subalgebra K Ω, R ≤ R' → (g : Ω)⁻¹ ∈ R' →
      Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => ((![1, g] i : R) : Ω) / ((![1, g] 1 : R) : Ω)) ≤ R' := by
    intro R' h1 h2
    apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · exact h1 hz
    · beta_reduce
      rw [div_eq_mul_inv]
      exact R'.mul_mem (h1 (![1, g] i).2) h2
  have e1 : ψ₀ (Subalgebra.inclusion hle g) = ψ g := DFunLike.congr_fun hc g
  rcases ValuationRing.isInteger_or_isInteger V (ψ g) with hi | hi
  · refine ⟨_, hle, ψ₀, Subalgebra.inclusion hle g, hg0, hinv, hsm, hc, hg0, hinv, ?_, fun R' h1 _ h3 => hmin R' h1 h3⟩
    rw [e1]; exact hi
  · refine ⟨_, hle, ψ₀, ⟨_, hinv⟩, hg0, hinv, hsm, hc, inv_ne_zero hg0, ?_, ?_, fun R' h1 h2 _ => hmin R' h1 h2⟩
    · change ((g : Ω)⁻¹)⁻¹ ∈ _
      rw [inv_inv]; exact hle g.2
    · have e2 : ψ₀ ⟨_, hinv⟩ = (ψ g)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← e1, ← map_mul, ← map_one ψ₀]
        congr 1
        exact Subtype.ext (inv_mul_cancel₀ hg0)
      rw [e2]; exact hi

set_option maxHeartbeats 800000 in

theorem exists_refine_extIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (S : Set Y.X) (P : PChart Xo c (algebraMap O c.F)) (T : CDVR) (io : c.F →+* T.Fr), IsOpen S → letI := io.toAlgebra; ∀ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] T.Fr) (z : FrPt Xo c T.Fr), (∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) → FrMap ψ (P.y e he) z → ExtIn Y S T io z.x → ∃ (P' : PChart Xo c (algebraMap O c.F)) (e' : P'.Ω) (he' : e' ∈ P'.es) (ψ' : P'.R e' →ₐ[c.F] T.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T (ψ' g)) ∧ FrMap ψ' (P'.y e' he') z ∧ ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) → letI := io₁.toAlgebra; ∀ (ψ₁ : P'.R e' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T₁ (ψ₁ g)) → FrMap ψ₁ (P'.y e' he') z₁ → ExtIn Y S T₁ io₁ z₁.x := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ Y S P T io hS
  letI := io.toAlgebra
  intro e he ψ z hgen hz hext
  classical
  obtain ⟨y', z₀, hz1, hz2, hz3, hz4⟩ := hext
  haveI : IsProper Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    haveI := isProper_str O N
    rw [← hs]; infer_instance
  let zR : Sp (P.R e) ⟶ Xo.XF c := pullback.lift (P.y e he).x (spMap (algebraMap c.F (P.R e)))
    (by rw [(P.y e he).x_over, sp_comp]; rfl)
  have hzR1 : zR ≫ pullback.fst _ _ = (P.y e he).x := pullback.lift_fst _ _ _
  have hzR2 : zR ≫ pullback.snd _ _ = spMap (algebraMap c.F (P.R e)) := pullback.lift_snd _ _ _
  have hb : (zR ≫ Y.j) ≫ Y.s = spMap ((algebraMap c.F (P.R e)).comp (algebraMap O c.F)) := by
    rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hzR2, sp_comp]
  have hz0 : spMap ψ.toRingHom ≫ zR = z₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hzR1, hz1, hz.1]
    · rw [Category.assoc, hzR2, hz2, sp_comp]
      exact congrArg spMap (RingHom.ext fun x => ψ.commutes x)
  obtain ⟨g, hg, hcs⟩ := exists_gens Y.s hS (zR ≫ Y.j) _ hb (algebraMap T.V T.Fr) ψ.toRingHom y'
    (by rw [← Category.assoc, hz0, hz3]) hz4
  obtain ⟨R₀, hle, ψ₀, h, hg0, hginv, hsm, hc, hh0, hhinv, hhV, hmin⟩ := exists_invert (V := T.V) (P.R e) g ψ hg
  obtain ⟨cs, hcs1, hcs2⟩ := hcs R₀ (Subalgebra.inclusion hle).toRingHom
    (IsUnit.of_mul_eq_one ⟨_, hginv⟩ (Subtype.ext (mul_inv_cancel₀ hg0)))
  obtain ⟨G, hGdef⟩ : ∃ G : Finset P.Ω, ∀ x, x ∈ G ↔ x ∈ P.gens ∨ ∃ u ∈ insert h cs, (u : P.Ω) = x :=
    ⟨P.gens ∪ (insert h cs).image Subtype.val, fun x => by rw [Finset.mem_union, Finset.mem_image]⟩
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => (hGdef g).2 (Or.inl hg)
  have hGc : ∀ x ∈ insert h cs, (x : P.Ω) ∈ G := fun x hx => (hGdef x).2 (Or.inr ⟨x, hx, rfl⟩)
  have hGh : (h : P.Ω) ∈ G := hGc h (Finset.mem_insert_self _ _)
  obtain ⟨he0, heB⟩ := P.es_mem e he
  let R' : Subalgebra c.F P.Ω := Algebra.adjoin c.F (insert (e * h)⁻¹ (G : Set P.Ω))
  have hGR : ∀ x ∈ G, x ∈ R' := fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hi : (e * h)⁻¹ ∈ R' := Algebra.subset_adjoin (Or.inl rfl)
  have heR : e ∈ R' := by
    refine (Subring.closure_le (t := R'.toSubring)).2 ?_ heB
    rintro x (⟨o, rfl⟩ | hx)
    · exact R'.algebraMap_mem _
    · exact hGR _ (hG hx)
  have hle' : P.R e ≤ R' := by
    apply Algebra.adjoin_le
    rintro x (rfl | hx)
    · have : e⁻¹ = h * (e * h)⁻¹ := by field_simp
      rw [this]; exact R'.mul_mem (hGR _ hGh) hi
    · exact hGR _ (hG hx)
  have h0' : R₀ ≤ R' := by
    refine hmin R' hle' (hGR _ hGh) ?_
    have : (h : P.Ω)⁻¹ = e * (e * h)⁻¹ := by field_simp
    rw [this]; exact R'.mul_mem heR hi
  have h'0 : R' ≤ R₀ := by
    apply Algebra.adjoin_le
    rintro x (rfl | hx)
    · rw [mul_inv]
      exact R₀.mul_mem (hle (Algebra.subset_adjoin (Or.inl rfl))) hhinv
    · rcases (hGdef x).1 hx with hx | hx
      · exact hle (Algebra.subset_adjoin (Or.inr hx))
      · obtain ⟨u, -, rfl⟩ := hx
        exact u.2
  have hsm' : Algebra.Smooth c.F R' := le_antisymm h0' h'0 ▸ hsm (P.sm e he)
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _
    (Subalgebra.inclusion hle') (P.y e he)
  have k1 : ∀ x : R', (x : P.Ω) ∈ G → InV T ((ψ₀.comp (Subalgebra.inclusion h'0)) x) := by
    intro x hx
    rcases (hGdef _).1 hx with hx' | hx'
    · have e2 := hgen ⟨x, Algebra.subset_adjoin (Or.inr hx')⟩ hx'
      have e3 := DFunLike.congr_fun hc ⟨x, Algebra.subset_adjoin (Or.inr hx')⟩
      rw [← e3] at e2
      exact e2
    · obtain ⟨u, hu, hux⟩ := hx'
      have e1 : Subalgebra.inclusion h'0 x = u := Subtype.ext hux.symm
      change ψ₀ (Subalgebra.inclusion h'0 x) ∈ (algebraMap T.V T.Fr).range
      rw [e1]
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hhV
      · exact hcs1 ψ₀.toRingHom (RingHom.ext fun x => DFunLike.congr_fun hc x) u hu
  have k2 : FrMap (ψ₀.comp (Subalgebra.inclusion h'0)) y₁ z := by
    refine frMap_cancel _ _ _ (Subalgebra.inclusion hle') _ (P.y e he) _ _ hy₁ ?_
    have : (ψ₀.comp (Subalgebra.inclusion h'0)).comp (Subalgebra.inclusion hle') = ψ :=
      AlgHom.ext fun x => DFunLike.congr_fun hc x
    exact this.symm ▸ hz
  have k3 : ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) →
      letI := io₁.toAlgebra; ∀ (ψ₁ : R' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr),
      (∀ g : R', (g : P.Ω) ∈ G → InV T₁ (ψ₁ g)) → FrMap ψ₁ y₁ z₁ → ExtIn Y S T₁ io₁ z₁.x := by
    intro T₁ io₁ hO
    letI := io₁.toAlgebra
    intro ψ₁ z₁ h2 hz₁
    have hz₁' := frMap_trans _ _ _ _ _ _ _ _ hy₁ hz₁
    obtain ⟨y₂, hy₂, hr₂⟩ := hcs2 T₁.V T₁.Fr (algebraMap T₁.V T₁.Fr) (IsFractionRing.injective _ _)
      (ψ₁.comp (Subalgebra.inclusion h0')).toRingHom
      (fun o => by
        have e1 := (ψ₁.comp (Subalgebra.inclusion hle')).commutes (algebraMap O c.F o)
        have e2 := hO o
        change algebraMap c.F T₁.Fr _ ∈ (algebraMap T₁.V T₁.Fr).range at e2
        rw [← e1] at e2
        exact e2)
      (fun x hx => h2 (Subalgebra.inclusion h0' x) (hGc x (Finset.mem_insert_of_mem hx)))
    refine ⟨y₂, spMap (ψ₁.comp (Subalgebra.inclusion hle')).toRingHom ≫ zR, ?_, ?_, ?_, hr₂⟩
    · rw [Category.assoc, hzR1]; exact hz₁'.1.symm
    · rw [Category.assoc, hzR2, sp_comp]
      exact congrArg spMap (RingHom.ext fun x => (ψ₁.comp (Subalgebra.inclusion hle')).commutes x)
    · rw [Category.assoc]; exact hy₂
  have hes : ∀ e' ∈ ({e * h} : Finset P.Ω), e' = e * h := fun e' he' => Finset.mem_singleton.1 he'
  let yy : ∀ e' ∈ ({e * h} : Finset P.Ω), FrPt Xo c (Algebra.adjoin c.F (insert e'⁻¹ (G : Set P.Ω))) :=
    fun e' he' => (hes e' he').symm ▸ y₁
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := {e * h}
            es_ne := Finset.singleton_nonempty _
            es_mem := fun e' he' => ?_
            sm := fun e' he' => ?_
            yg := P.yg
            y := yy
            gen := fun e' he' => ?_
            int := fun e' he' => ?_ }, e * h, Finset.mem_singleton_self _,
            ψ₀.comp (Subalgebra.inclusion h'0), k1, k2, k3⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · obtain rfl := hes e' he'
    exact ⟨mul_ne_zero he0 hh0, mul_mem (Subring.closure_mono (Set.union_subset_union_right _ hG) heB)
      (Subring.subset_closure (Or.inr hGh))⟩
  · obtain rfl := hes e' he'
    exact hsm'
  · obtain rfl := hes e' he'
    exact frMap_cancel _ _ _ (Subalgebra.inclusion hle') _ (P.y e he) _ _ hy₁ (P.gen e he)
  · obtain rfl := hes e' he'
    intro T₁ io₁
    letI := io₁.toAlgebra
    intro ψ₁ h1 h2 z₁ hz₁
    refine P.int e he T₁ io₁ (ψ₁.comp (Subalgebra.inclusion hle')) h1 (fun g hg => ?_) z₁
      (frMap_trans _ _ _ _ _ _ _ _ hy₁ hz₁)
    exact h2 (Subalgebra.inclusion hle' g) (hG hg)

end GlobalTheory.GoodRefine
