import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodularStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestZar

theorem idem_unit {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) (h : IsUnit u) : u = 1 :=
  h.mul_left_cancel (by rw [mul_one]; exact hu)

theorem factor_one {R R' ι : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : ι → R) (hb : ∀ i, IsIdempotentElem (b i))
    (S : Finset ι) (h : g (∏ i ∈ S, b i) = 1) {i : ι} (hi : i ∈ S) : g (b i) = 1 :=
  idem_unit ((hb i).map g) (isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem b hi)) (h ▸ isUnit_one))

theorem span_of_nil {R P ι : Type} [CommRing R] [CommRing P] (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) (g : ι → R)
    (π : P →+* R ⧸ I) (e : ι → P) (he : Ideal.span (Set.range e) = ⊤)
    (h : ∀ i, π (e i) = Ideal.Quotient.mk I (g i)) : Ideal.span (Set.range g) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) = ⊤ := by
    have e1 : (Ideal.Quotient.mk I) ∘ g = π ∘ e := funext fun i => (h i).symm
    rw [Ideal.map_span, ← Set.range_comp, e1, Set.range_comp, ← Ideal.map_span, he, Ideal.map_top]
  have h2 : (1 : R ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (hI _ hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Gen

open GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
  {R₀ : Type} [CommRing R₀] (c : R₀ →+* b.R) (r : ℕ)
  {C : Type*} [Category C] (G : C ⥤ Thick (F.cr b ht κ))

def locModG {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (f : Fin m → (G.obj T').B) (hf : Ideal.span (Set.range f) = ⊤)
    (h1 : ∀ S, ∀ k ∈ S, (G.map (lam S)).φ (f k) = 1)
    (hs : ∀ S, ∀ y ∈ (G.obj (Lc S)).pdPow r, ∃ x ∈ (G.obj T').pdPow r, (G.map (lam S)).φ x = y)
    (hk : ∀ S x, (G.map (lam S)).φ x = 0 → (∏ k ∈ S, f k) * x = 0) :
    LocMod (G ⋙ (pdS (F.cr b ht κ) c r).fn) T' Lc lam where
  Λ := (G.obj T').B
  f := f
  span := hf
  ρ₀ := mulR c r (G.obj T')
  ρ S := (mulR c r (G.obj (Lc S))).comp (G.map (lam S)).φ
  lam_ρ S a x := Subtype.ext (map_mul (G.map (lam S)).φ a (show (G.obj T').B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : (G.map t).φ.comp (G.map (lam S)).φ = (G.map (lam S')).φ := by
      have := congrArg Thick.Hom.φ (congrArg G.map ht')
      rw [G.map_comp] at this
      exact this
    refine Subtype.ext ?_
    change (G.map t).φ ((G.map (lam S)).φ a * (show (G.obj (Lc S)).B from x.1)) =
      (G.map (lam S')).φ a * (G.map t).φ (show (G.obj (Lc S)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply (G.map t).φ, e]
  unit S k hk' := by
    change Function.Bijective (mulR c r (G.obj (Lc S)) ((G.map (lam S)).φ (f k)))
    rw [h1 S k hk', map_one]
    exact Function.bijective_id
  surj S y := by
    obtain ⟨x, hx, e⟩ := hs S y.1 y.2
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    rw [pow_zero, map_one]
    exact Subtype.ext e.symm
  ker S x hx := by
    have h0 : (G.map (lam S)).φ (show (G.obj T').B from x.1) = 0 := congrArg Subtype.val hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact hk S _ h0

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem step_onto {A B : PAlg l} (lam : A ⟶ B) (k : Bool) (n r : ℕ) (hs : Function.Surjective (mapAcr lam n))
    {y : B.Acr n} (hy : y ∈ fil (DD k B n) r) : ∃ x ∈ fil (DD k A n) r, mapAcr lam n x = y := by
  have hA := (GlobalTheory.T.period_ring_base_change_from_universal A n).2.2.2.2.1 k r
  have hB := (GlobalTheory.T.period_ring_base_change_from_universal B n).2.2.2.2.1 k r
  have e : (mapAcr lam n).comp (mapAcr A.fromBase n) = mapAcr B.fromBase n :=
    RingHom.ext fun x => mapAcr_fromBase lam n x
  rw [hB, ← e, ← Ideal.map_map, ← hA] at hy
  exact (Ideal.mem_map_iff_of_surjective _ hs).1 hy

theorem span_acr (A : PAlg l) (n : ℕ) {m : ℕ} (e : Fin m → A.A) (he : Ideal.span (Set.range e) = ⊤) :
    Ideal.span (Set.range fun i => A.toAcr n (WittVector.teichmuller l (e i))) = ⊤ := by
  obtain ⟨⟨π, hπ, -⟩, -, -, -, -, hnil, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  exact span_of_nil (A.PFil n) (fun x hx => (hnil x hx).1) _ π e he fun i => hπ _

theorem acr_teich_one {A B : PAlg l} (f : A ⟶ B) (n : ℕ) {a : A.A} (h : Hom.f f a = 1) :
    mapAcr f n (A.toAcr n (WittVector.teichmuller l a)) = 1 := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_one, map_one]

theorem acr_teich_prod (A : PAlg l) (n : ℕ) {ι : Type} (S : Finset ι) (a : ι → A.A) :
    A.toAcr n (WittVector.teichmuller l (∏ i ∈ S, a i)) = ∏ i ∈ S, A.toAcr n (WittVector.teichmuller l (a i)) := by
  rw [map_prod, map_prod]

section Fac

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def facObj (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : El (F.pt κ) :=
  ⟨⟨A', h⟩, (F.pt κ).map lam T'.2⟩

def facHom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : T' ⟶ facObj F κ T' A' lam h :=
  ⟨ObjectProperty.homMk lam, rfl⟩

theorem facHom_hom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) :
    (facHom F κ T' A' lam h).1.hom = lam := rfl

theorem fac_univ (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) (T'' : El (F.pt κ)) (ψ : T' ⟶ T'')
    (hu : ∃! χ : A' ⟶ T''.1.obj, lam ≫ χ = ψ.1.hom) :
    ∃! χ : facObj F κ T' A' lam h ⟶ T'', facHom F κ T' A' lam h ≫ χ = ψ := by
  obtain ⟨χ, hχ, huniq⟩ := hu
  refine ⟨⟨ObjectProperty.homMk χ, ?_⟩, Subtype.ext (ObjectProperty.hom_ext _ hχ), fun χ' h' =>
    Subtype.ext (ObjectProperty.hom_ext _ (huniq χ'.1.hom (congrArg (fun z => z.1.hom) h')))⟩
  change (F.pt κ).map χ ((F.pt κ).map lam T'.2) = T''.2
  rw [← Functor.map_comp_apply, hχ]
  exact ψ.2

theorem fac_loc (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ} (b : Fin m → T'.1.obj.A)
    (hspan : Ideal.span (Set.range b) = ⊤) (A' : Finset (Fin m) → PAlg l) (lam : ∀ S, T'.1.obj ⟶ A' S)
    (ht : ∀ S, (A' S).IsTest) (h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1)
    (hs : ∀ S, Function.Surjective (mapAcr (lam S) n))
    (hk : ∀ S x, mapAcr (lam S) n x = 0 → T'.1.obj.toAcr n (WittVector.teichmuller l (∏ i ∈ S, b i)) * x = 0) :
    Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T'
      (fun S => facObj F κ T' (A' S) (lam S) (ht S)) fun S => facHom F κ T' (A' S) (lam S) (ht S)) := by
  have hf : Ideal.span (Set.range fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) = ⊤ := span_acr _ n b hspan
  have hk' : ∀ S x, mapAcr (lam S) n x = 0 →
      (∏ i ∈ S, T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) * x = 0 := fun S x hx => by
    have h := hk S x hx
    rw [acr_teich_prod] at h
    exact h
  exact ⟨locModG (F := F) (b := bs l k n) (ht := rfl) (κ := κb κ k n) ((base l).cris n) r (gT F κ k n) T'
    (fun S => facObj F κ T' (A' S) (lam S) (ht S)) (fun S => facHom F κ T' (A' S) (lam S) (ht S))
    (fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) hf
    (fun S i hi => acr_teich_one (lam S) n (h1 S i hi))
    (fun S y hy => step_onto (lam S) k n r (hs S) hy) hk'⟩

theorem factors (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ}
    (b : Fin m → T'.1.obj.A) (hb : ∀ i, IsIdempotentElem (b i)) (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (Lc' : Finset (Fin m) → El (F.pt κ)) (lamE : ∀ S, T' ⟶ Lc' S),
      (∀ S, ∀ i ∈ S, Hom.f (lamE S).1.hom (b i) = 1) ∧
      (∀ S (T'' : El (F.pt κ)) (ψ : T' ⟶ T''), (∀ i ∈ S, Hom.f ψ.1.hom (b i) = 1) → ∃! χ : Lc' S ⟶ T'', lamE S ≫ χ = ψ) ∧
      Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T' Lc' lamE) := by
  have ha : ∀ S : Finset (Fin m), IsIdempotentElem (∏ i ∈ S, b i) := fun S =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h h' => h.mul h') IsIdempotentElem.one fun i _ => hb i
  choose A' lam htest hlam huniv hacr using fun S => GlobalTheory.T.idempotent_localization_universal T'.1.obj (∏ i ∈ S, b i) (ha S)
  have h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1 := fun S i hi => factor_one (Hom.f (lam S)) b hb S (hlam S) hi
  have ht : ∀ S, (A' S).IsTest := fun S => htest S T'.1.property
  refine ⟨fun S => facObj F κ T' (A' S) (lam S) (ht S), fun S => facHom F κ T' (A' S) (lam S) (ht S), h1,
    fun S T'' ψ h => fac_univ F κ T' (A' S) (lam S) (ht S) T'' ψ (huniv S T''.1.obj ψ.1.hom ?_),
    fac_loc F κ k n r T' b hspan A' lam ht h1 (fun S => (hacr S n).1) fun S => (hacr S n).2⟩
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi => h i hi

end Fac

theorem chart_of_one {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n : ℕ)
    {T T₁ : El (F.pt κ)} (ψ : T ⟶ T₁) (s : T.1.obj.U) (a : T.1.obj.A) (ha : T.1.obj.sharp a ∈ Ideal.span {s})
    (hcov : ∀ (B' : CommRingCat) (φ : CommRingCat.of T.1.obj.U ⟶ B'), IsUnit (φ.hom s) →
      ∃ α, (𝒜.V α).In (F.Pt.map φ T.2.1))
    (h : Hom.f ψ.1.hom a = 1) : ∃ α, (𝒜.V α).In ((gT F κ k n).obj T₁).y.1.2 := by
  have hu : IsUnit ((CommRingCat.ofHom (mapU ψ.1.hom)).hom s) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have h2 := congrArg (mapU ψ.1.hom) hc
    rw [map_mul, mapU_sharp, h, map_one] at h2
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
  obtain ⟨α, hα⟩ := hcov _ _ hu
  have hpt : F.Pt.map (CommRingCat.ofHom (mapU ψ.1.hom)) T.2.1 = T₁.2.1 := congrArg Subtype.val ψ.2
  rw [hpt] at hα
  exact ⟨α, (𝒜.V α).in_map (CommRingCat.ofHom (uJ k T₁.1.obj n)) hα⟩

theorem zarCov_test : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d)
    (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn)
      fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 k n r
  refine ⟨fun T T' φ h => (GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜
    (Fact.out : l.Prime).ne_zero r).1 ((gT F κ k n).map φ) h, fun T => ?_⟩
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of T.1.obj.U) T.2.1
  obtain ⟨e, hidem, hspan, hes⟩ := GlobalTheory.T.idempotent_refinement_of_unimodular T.1.obj T.1.property s hs
  refine ⟨m, fun i _ ψ => Hom.f ψ.1.hom (e i) = 1, fun i T₁ T₂ ψ χ h => ?_,
    fun i T₁ ψ h => chart_of_one F κ 𝒜 k n ψ (s i) (e i) (hes i) (hcov i) h, fun T' φ => ?_⟩
  · have h' : Hom.f ψ.1.hom (e i) = 1 := h
    have e1 : Hom.f (ψ ≫ χ).1.hom (e i) = Hom.f χ.1.hom (Hom.f ψ.1.hom (e i)) := rfl
    exact e1.trans (by rw [h', map_one])
  have hspan' : Ideal.span (Set.range fun i => Hom.f φ.1.hom (e i)) = ⊤ := by
    have h := congrArg (Ideal.map (Hom.f φ.1.hom)) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨Lc', lamE, h1, h2, h3⟩ := factors F κ k n r T' (fun i => Hom.f φ.1.hom (e i))
    (fun i => (hidem i).map (Hom.f φ.1.hom)) hspan'
  exact ⟨Lc', lamE, fun S i hi => h1 S i hi, fun S T'' ψ h => h2 S T'' ψ fun i hi => h i hi, h3⟩

end GlobalTheory.CompanionTheory.TestZar
