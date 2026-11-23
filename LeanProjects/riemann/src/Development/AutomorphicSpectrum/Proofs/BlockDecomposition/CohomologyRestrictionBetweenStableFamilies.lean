import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.ZarCosieve

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem nil_of_mem (T : Thick (nlFun γ p X q κ)) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

theorem span_lift (T : Thick (nlFun γ p X q κ)) {m : ℕ} (f : Fin m → T.B) (s : Fin m → T.B ⧸ T.J)
    (hf : ∀ k, Ideal.Quotient.mk T.J (f k) = s k) (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range f) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) = ⊤ := by
    rw [Ideal.map_span, ← Set.range_comp, ← hs]
    congr 2
    exact funext hf
  have h2 : (1 : T.B ⧸ T.J) ∈ Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ T.J := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (nil_of_mem T hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

theorem locH_φ (T : Thick (nlFun γ p X q κ)) (a : T.B) :
    (locH T a).φ = algebraMap T.B (Localization.Away a) := rfl

theorem comp_φ {T T' T'' : Thick (nlFun γ p X q κ)} (f : T ⟶ T') (g : T' ⟶ T'') : (f ≫ g).φ = g.φ.comp f.φ := rfl

theorem locT_univ (T : Thick (nlFun γ p X q κ)) (a : T.B) {T'' : Thick (nlFun γ p X q κ)} (ψ : T ⟶ T'')
    (hu : IsUnit (ψ.φ a)) : ∃! χ : locT T a ⟶ T'', locH T a ≫ χ = ψ := by
  let l : Localization.Away a →+* T''.B := IsLocalization.Away.lift a hu
  have hl : l.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := IsLocalization.Away.lift_comp a hu
  have hdp : IsDPMorphism (locD T a) T''.δ l :=
    (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ _ (locD T a) (locD_dp T a)).2 T''.δ l (hl ▸ ψ.dp)
  have hle : T.J.map (algebraMap T.B (Localization.Away a)) ≤ T''.J.comap l :=
    Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf ψ l hl hdp hle, hom_ext hl, fun χ hχ => hom_ext ?_⟩
  let χ' : Localization.Away a →+* T''.B := χ.φ
  have h1 : χ'.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := congrArg Thick.Hom.φ hχ
  have h2 : χ' = l := IsLocalization.ringHom_ext (Submonoid.powers a) (h1.trans hl.symm)
  exact h2

theorem pdPow_locT (T : Thick (nlFun γ p X q κ)) (a : T.B) (r : ℕ) :
    (locT T a).pdPow r = (T.pdPow r).map (algebraMap T.B (Localization.Away a)) :=
  (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ (algebraMap T.B (Localization.Away a)) _ (locD_dp T a)).1 r

theorem exists_cover (𝒱 : Set X.Opens) (T : Thick (nlFun γ p X q κ)) (h : InU (sSup 𝒱) T) :
    ∃ (m : ℕ) (s : Fin m → T.B ⧸ T.J), Ideal.span (Set.range s) = ⊤ ∧
      ∀ k, ∃ V ∈ 𝒱, ∀ (T' : Thick (nlFun γ p X q κ)) (ψ : T ⟶ T'),
        IsUnit (Ideal.quotientMap T'.J ψ.φ ψ.hle (s k)) → InU V T' := by
  classical
  have hcov : ∀ x : PrimeSpectrum (T.B ⧸ T.J), ∃ V ∈ 𝒱, ∃ g : T.B ⧸ T.J, x ∈ PrimeSpectrum.basicOpen g ∧
      ∀ z : PrimeSpectrum (T.B ⧸ T.J), z ∈ PrimeSpectrum.basicOpen g → z ∈ (pt T ⁻¹ᵁ V : (Spec (CommRingCat.of (T.B ⧸ T.J))).Opens) := by
    intro x
    have hx : x ∈ (pt T ⁻¹ᵁ (sSup 𝒱) : (Spec (CommRingCat.of (T.B ⧸ T.J))).Opens) :=
      h (show x ∈ (⊤ : (Spec (CommRingCat.of (T.B ⧸ T.J))).Opens) from trivial)
    have hx' : (pt T) x ∈ sSup 𝒱 := hx
    obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx'
    let U : TopologicalSpace.Opens (PrimeSpectrum (T.B ⧸ T.J)) := pt T ⁻¹ᵁ V
    obtain ⟨v, ⟨g, rfl⟩, hxv, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show x ∈ (U : Set (PrimeSpectrum (T.B ⧸ T.J))) from hxV) U.isOpen
    exact ⟨V, hV, g, hxv, fun z hz => hsub hz⟩
  choose V hV g hxg hsub using hcov
  have htop : Ideal.span (Set.range g) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine top_le_iff.1 fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxg x⟩
  obtain ⟨s', hs', hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 htop
  refine ⟨s'.card, fun k => (s'.equivFin.symm k : T.B ⧸ T.J), ?_, fun k => ?_⟩
  · have : Set.range (fun k => (s'.equivFin.symm k : T.B ⧸ T.J)) = (s' : Set (T.B ⧸ T.J)) := by
      ext e
      constructor
      · rintro ⟨k, rfl⟩
        exact (s'.equivFin.symm k).2
      · intro he
        exact ⟨s'.equivFin ⟨e, he⟩, by simp⟩
    rw [this, hspan]
  obtain ⟨x, hx⟩ := hs' (s'.equivFin.symm k).2
  refine ⟨V x, hV x, fun T' ψ hu z _ => ?_⟩
  rw [pt_hom ψ]
  refine hsub x (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J ψ.φ ψ.hle)) z) ?_
  rw [hx]
  change _ ∉ _
  intro hmem
  have : Ideal.quotientMap T'.J ψ.φ ψ.hle (s'.equivFin.symm k : T.B ⧸ T.J) ∈ z.asIdeal := hmem
  exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ this hu)

theorem Q_locT {Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))} (hQ : Used Q₀) (T : Thick (nlFun γ p X q κ))
    (hT : Q₀ T) (a : T.B) : Q₀ (locT T a) := by
  rcases hQ with ⟨hp, l, s, rfl⟩ | ⟨hp, rfl | rfl⟩
  · have key : ∀ (r : ℕ) (x : Localization.Away a), (l : Localization.Away a) * x ∈
        (T.pdPow r).map (algebraMap T.B (Localization.Away a)) →
        x ∈ (T.pdPow r).map (algebraMap T.B (Localization.Away a)) := by
      intro r x hx
      obtain ⟨⟨y, s'⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) x
      have h1 : algebraMap T.B (Localization.Away a) ((l : T.B) * y) ∈
          (T.pdPow r).map (algebraMap T.B (Localization.Away a)) := by
        rw [map_mul, map_natCast, ← hy, ← mul_assoc]
        exact Ideal.mul_mem_right _ _ hx
      obtain ⟨m, hm, hm'⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers a) _ _ _).1 h1
      have h2 : m * y ∈ T.pdPow r := hT.2 r _ (by rw [mul_left_comm]; exact hm')
      have h3 := Ideal.mem_map_of_mem (algebraMap T.B (Localization.Away a)) h2
      rw [map_mul, ← hy, ← mul_assoc, mul_comm _ x, mul_assoc] at h3
      have hu : IsUnit (algebraMap T.B (Localization.Away a) m * algebraMap T.B (Localization.Away a) s') :=
        (IsLocalization.map_units _ ⟨m, hm⟩).mul (IsLocalization.map_units _ s')
      exact (Ideal.mul_unit_mem_iff_mem _ hu).1 h3
    refine ⟨by rw [pdPow_locT, hT.1, Ideal.map_bot], fun r x hx => ?_⟩
    rw [pdPow_locT] at hx ⊢
    exact key r x hx
  · trivial
  · change ((algebraMap T.B (Localization.Away a)).comp T.i).Flat
    have h1 : (algebraMap T.B (Localization.Away a)).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers a))
    exact RingHom.Flat.comp hT h1

variable {Q' : ObjectProperty (Thick (nlFun γ p X q κ))}

abbrev lc (T : Q'.FullSubcategory) (g : T.obj.B) (hq : Q' (locT T.obj g)) : Q'.FullSubcategory := ⟨locT T.obj g, hq⟩

abbrev lch (T : Q'.FullSubcategory) (g : T.obj.B) (hq : Q' (locT T.obj g)) : T ⟶ lc T g hq :=
  ObjectProperty.homMk (locH T.obj g)

def LocI (a : IdF (sP Q').A) : Prop :=
  ∀ (T : Q'.FullSubcategory) (g : T.obj.B) (hq : Q' (locT T.obj g)),
    (a.S (lc T g hq) : Ideal (Localization.Away g)) =
      Ideal.map (algebraMap T.obj.B (Localization.Away g)) (a.S T : Ideal T.obj.B)

def mkLoc (F : Q'.FullSubcategory ⥤ ModuleCat.{0} R)
    (μ : ∀ T : Q'.FullSubcategory, T.obj.B →+* Module.End R (F.obj T))
    (hμ : ∀ {T T' : Q'.FullSubcategory} (t : T ⟶ T') (a : T.obj.B) (x : F.obj T),
      (F.map t).hom (μ T a x) = μ T' (t.hom.φ a) ((F.map t).hom x))
    (hs : ∀ (T : Q'.FullSubcategory) (g : T.obj.B) (hq : Q' (locT T.obj g)) (y : F.obj (lc T g hq)),
      ∃ (n : ℕ) (x : F.obj T), μ _ ((locH T.obj g).φ (g ^ n)) y = (F.map (lch T g hq)).hom x)
    (hk : ∀ (T : Q'.FullSubcategory) (g : T.obj.B) (hq : Q' (locT T.obj g)) (x : F.obj T),
      (F.map (lch T g hq)).hom x = 0 → ∃ n : ℕ, μ T (g ^ n) x = 0)
    (T : Q'.FullSubcategory) {m : ℕ} (f : Fin m → T.obj.B) (hf : Ideal.span (Set.range f) = ⊤)
    (hq : ∀ S : Finset (Fin m), Q' (locT T.obj (∏ k ∈ S, f k))) :
    B.LocMod F T (fun S => lc T _ (hq S)) (fun S => lch T _ (hq S)) where
  Λ := T.obj.B
  f := f
  span := hf
  ρ₀ := μ T
  ρ S := (μ _).comp (locH T.obj (∏ k ∈ S, f k)).φ
  lam_ρ S a x := hμ _ a x
  tr_ρ S S' t ht a x := by
    have e : t.hom.φ.comp (locH T.obj (∏ k ∈ S, f k)).φ = (locH T.obj (∏ k ∈ S', f k)).φ :=
      congrArg (fun u => u.hom.φ) ht
    refine (hμ t _ x).trans ?_
    change μ _ ((t.hom.φ.comp (locH T.obj (∏ k ∈ S, f k)).φ) a) _ = _
    rw [e]
    rfl
  unit S k hk := by
    have h : IsUnit (algebraMap T.obj.B (Localization.Away (∏ k ∈ S, f k)) (∏ k ∈ S, f k)) :=
      IsLocalization.Away.algebraMap_isUnit _
    have h' : IsUnit (algebraMap T.obj.B (Localization.Away (∏ k ∈ S, f k)) (f k)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f hk)) h
    exact (Module.End.isUnit_iff _).1 (IsUnit.map (μ (lc T _ (hq S))) h')
  surj S y := hs T _ _ y
  ker S x h := hk T _ _ x h

def mulQ (a b : IdF (sP Q').A) (T : Q'.FullSubcategory) : T.obj.B →+* Module.End R (sqM a b T) where
  toFun c := (LinearMap.mulLeft R (Ideal.Quotient.mk (b.S T) c)).restrict fun x hx => Ideal.mul_mem_left _ _ hx
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' c c' := LinearMap.ext fun x => Subtype.ext (by simp [mul_assoc])
  map_zero' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_add' c c' := LinearMap.ext fun x => Subtype.ext (by simp [add_mul])

theorem mulQ_map (a b : IdF (sP Q').A) {T T' : Q'.FullSubcategory} (t : T ⟶ T') (c : T.obj.B) (x : sqM a b T) :
    ((sq a b).map t).hom (mulQ a b T c x) = mulQ a b T' (t.hom.φ c) (((sq a b).map t).hom x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk (b.S T') (show T'.obj.B from t.hom.φ (c * (show T.obj.B from y))) =
    Ideal.Quotient.mk (b.S T') (show T'.obj.B from t.hom.φ c * t.hom.φ (show T.obj.B from y))
  rw [map_mul]

def locSq (a b : IdF (sP Q').A) (ha : LocI a) (hb : LocI b) (T : Q'.FullSubcategory) {m : ℕ} (f : Fin m → T.obj.B)
    (hf : Ideal.span (Set.range f) = ⊤) (hq : ∀ S : Finset (Fin m), Q' (locT T.obj (∏ k ∈ S, f k))) :
    B.LocMod (sq a b) T (fun S => lc T _ (hq S)) (fun S => lch T _ (hq S)) :=
  mkLoc (sq a b) (fun T => mulQ a b T) (fun t c x => mulQ_map a b t c x) (by
    intro T g hq y
    obtain ⟨y, hy⟩ := y
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    have hz' : (show Localization.Away g from z) ∈
        Ideal.map (algebraMap T.obj.B (Localization.Away g)) (a.S T : Ideal T.obj.B) := by
      rw [← ha T g hq]; exact hz
    obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) _).1 hz'
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, ⟨Ideal.Quotient.mk _ x.1, Ideal.mem_map_of_mem _ x.2⟩, Subtype.ext ?_⟩
    have e : algebraMap T.obj.B (Localization.Away g) (g ^ n) * (show Localization.Away g from z) =
        algebraMap T.obj.B (Localization.Away g) x.1 := by
      rw [mul_comm, ← hx]
      exact congrArg (fun u => (show Localization.Away g from z) * algebraMap T.obj.B (Localization.Away g) u) hn
    change Ideal.Quotient.mk (b.S (lc T g hq)) (show (sP Q').A.obj (lc T g hq) from
        algebraMap T.obj.B (Localization.Away g) (g ^ n) * (show Localization.Away g from z)) =
      Ideal.Quotient.mk (b.S (lc T g hq)) (show (sP Q').A.obj (lc T g hq) from
        algebraMap T.obj.B (Localization.Away g) x.1)
    exact congrArg (Ideal.Quotient.mk (b.S (lc T g hq))) e) (by
    intro T g hq x h
    obtain ⟨x, hx⟩ := x
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have h0 : Ideal.Quotient.mk (b.S (lc T g hq)) (show (sP Q').A.obj (lc T g hq) from
        algebraMap T.obj.B (Localization.Away g) (show T.obj.B from z)) = 0 := congrArg Subtype.val h
    have h1 : algebraMap T.obj.B (Localization.Away g) (show T.obj.B from z) ∈
        Ideal.map (algebraMap T.obj.B (Localization.Away g)) (b.S T : Ideal T.obj.B) := by
      rw [← hb T g hq]; exact Ideal.Quotient.eq_zero_iff_mem.1 h0
    obtain ⟨_, ⟨n, rfl⟩, hm⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g) _ _ _).1 h1
    refine ⟨n, Subtype.ext ?_⟩
    change Ideal.Quotient.mk (b.S T) (show (sP Q').A.obj T from g ^ n * (show T.obj.B from z)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hm) T f hf hq

def mulO (T : Q'.FullSubcategory) : T.obj.B →+* Module.End R ((CH.modF (sP Q').A).obj T) :=
  (Algebra.lmul R ((sP Q').A.obj T)).toRingHom

def locO (T : Q'.FullSubcategory) {m : ℕ} (f : Fin m → T.obj.B)
    (hf : Ideal.span (Set.range f) = ⊤) (hq : ∀ S : Finset (Fin m), Q' (locT T.obj (∏ k ∈ S, f k))) :
    B.LocMod (CH.modF (sP Q').A) T (fun S => lc T _ (hq S)) (fun S => lch T _ (hq S)) :=
  mkLoc (CH.modF (sP Q').A) mulO (fun {T T'} t c x => map_mul t.hom.φ c (show T.obj.B from x)) (by
    intro T g hq y
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (Submonoid.powers g) (show Localization.Away g from y)
    obtain ⟨n, hn⟩ := s.2
    refine ⟨n, x, ?_⟩
    change algebraMap T.obj.B (Localization.Away g) (g ^ n) * (show Localization.Away g from y) =
      algebraMap T.obj.B (Localization.Away g) x
    rw [mul_comm, ← hx]
    exact congrArg (fun u => (show Localization.Away g from y) * algebraMap T.obj.B (Localization.Away g) u) hn) (by
    intro T g hq x h
    have h0 : algebraMap T.obj.B (Localization.Away g) (show T.obj.B from x) = 0 := h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 h0
    exact ⟨n, hn⟩) T f hf hq

theorem locI_fil (r : ℤ) : LocI (sFil Q' r) := fun T g _ => pdPow_locT T.obj g r.toNat

theorem locI_std (r : Option ℤ) (c : R) : LocI (stdI Q' r c) := by
  intro T g hq
  have e : Ideal.map (algebraMap T.obj.B (Localization.Away g)) (Ideal.span {T.obj.i c}) =
      Ideal.span {(locT T.obj g).i c} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  cases r with
  | none =>
    change (⊥ : Ideal (Localization.Away g)) ⊔ Ideal.span {(locT T.obj g).i c} =
      Ideal.map (algebraMap T.obj.B (Localization.Away g)) ((⊥ : Ideal T.obj.B) ⊔ Ideal.span {T.obj.i c})
    rw [Ideal.map_sup, Ideal.map_bot, e]
    rfl
  | some r =>
    change (locT T.obj g).pdPow r.toNat ⊔ Ideal.span {(locT T.obj g).i c} =
      Ideal.map (algebraMap T.obj.B (Localization.Away g)) (T.obj.pdPow r.toNat ⊔ Ideal.span {T.obj.i c})
    rw [Ideal.map_sup, e, pdPow_locT]

theorem zarCov (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀) (𝒱 : Set X.Opens)
    (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T')
    (F : Q'.FullSubcategory ⥤ ModuleCat.{0} R)
    (hF : ∀ (T : Q'.FullSubcategory) {m : ℕ} (f : Fin m → T.obj.B), Ideal.span (Set.range f) = ⊤ →
      ∀ hq : ∀ S : Finset (Fin m), Q' (locT T.obj (∏ k ∈ S, f k)),
      Nonempty (B.LocMod F T (fun S => lc T _ (hq S)) (fun S => lch T _ (hq S)))) :
    B.ZarCov F fun T => St Q₀ 𝒱 T.obj := by
  refine ⟨fun T T' t ⟨_, V, hV, hT⟩ => ⟨(h' _ T'.property).1, V, hV, inU_hom t.hom hT⟩, fun T => ?_⟩
  obtain ⟨-, W, hW, hin⟩ := h' _ T.property
  obtain rfl : W = sSup 𝒱 := hW
  obtain ⟨m, s, hs, hcov⟩ := exists_cover 𝒱 T.obj hin
  choose f hf using fun k => Ideal.Quotient.mk_surjective (s k)
  have hspan : Ideal.span (Set.range f) = ⊤ := span_lift T.obj f s hf hs
  refine ⟨m, fun k _ ψ => IsUnit (ψ.hom.φ (f k)), fun k T₁ T₂ ψ χ h => h.map χ.hom.φ, fun k T₁ ψ hu => ?_, fun T' φ => ?_⟩
  · obtain ⟨V, hV, hVin⟩ := hcov k
    refine ⟨(h' _ T₁.property).1, V, hV, hVin _ ψ.hom ?_⟩
    rw [← hf k]
    exact hu.map (Ideal.Quotient.mk T₁.obj.J)
  have hq : ∀ S : Finset (Fin m), Q' (locT T'.obj (∏ k ∈ S, φ.hom.φ (f k))) := fun S =>
    hc _ _ (locH _ _) T'.property (Q_locT hQ _ (h' _ T'.property).1 _)
  have hspan' : Ideal.span (Set.range fun k => φ.hom.φ (f k)) = ⊤ := by
    have h := congrArg (Ideal.map φ.hom.φ) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  refine ⟨fun S => lc T' _ (hq S), fun S => lch T' _ (hq S), fun S k hk => ?_, fun S T'' ψ h => ?_, hF T' _ hspan' hq⟩
  · have h : IsUnit (algebraMap T'.obj.B (Localization.Away (∏ k ∈ S, φ.hom.φ (f k))) (∏ k ∈ S, φ.hom.φ (f k))) :=
      IsLocalization.Away.algebraMap_isUnit _
    have h2 : IsUnit (algebraMap T'.obj.B (Localization.Away (∏ k ∈ S, φ.hom.φ (f k))) (φ.hom.φ (f k))) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun k => φ.hom.φ (f k)) hk)) h
    exact h2
  have hu : IsUnit (ψ.hom.φ (∏ k ∈ S, φ.hom.φ (f k))) := by
    rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one h
  obtain ⟨χ, hχ, hχu⟩ := locT_univ T'.obj _ ψ.hom hu
  refine ⟨ObjectProperty.homMk χ, ObjectProperty.hom_ext _ hχ, fun χ' h' => ObjectProperty.hom_ext _ (hχu _ ?_)⟩
  exact congrArg (fun u => u.hom) h'

theorem bij_of_upTo {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N)
    (h : UpTo (1 : R) f) : Function.Bijective f :=
  ⟨(injective_iff_map_eq_zero f).2 fun x hx => by simpa using h.1 x hx, fun y => by
    obtain ⟨x, hx⟩ := h.2 y
    exact ⟨x, by simpa using hx⟩⟩

theorem onto {Q₁ : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q₁ ≤ Q') :
    B.Onto (ObjectProperty.ιOfLE h) fun T : Q'.FullSubcategory => Q₁ T.obj where
  full := inferInstance
  faithful := inferInstance
  mem T := T.property
  ess T hT := ⟨⟨T.obj, hT⟩, ⟨Iso.refl _⟩⟩

theorem mor_eq {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}
    (G : C' ⥤ C) (m m' : CH.Mor F F' (RingHom.id R)) (h1 : m.G = G) (h2 : m'.G = G)
    (h : ∀ T (x : F.obj (G.obj T)), m.τ T (h1.symm ▸ x) = m'.τ T (h2.symm ▸ x)) : m = m' := by
  obtain ⟨G₁, τ, n⟩ := m
  obtain ⟨G₂, τ', n'⟩ := m'
  obtain rfl : G₁ = G := h1
  obtain rfl : G₂ = G₁ := h2
  obtain rfl : τ = τ' := funext fun T => LinearMap.ext (h T)
  rfl

theorem bij_restrict {Q₁ : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q₁ ≤ Q') (F : Q'.FullSubcategory ⥤ ModuleCat.{0} R)
    (hZ : B.ZarCov F fun T => Q₁ T.obj) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict F (ObjectProperty.ιOfLE h)).pull j) :=
  bij_of_upTo _ (B.P.zar F _ (ObjectProperty.ιOfLE h) (onto h) hZ j j le_rfl)

theorem bij_of_eq {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}
    (m m' : CH.Mor F F' (RingHom.id R)) (e : m = m') (j : ℕ) (h : Function.Bijective (m'.pull j)) :
    Function.Bijective (m.pull j) := e ▸ h

theorem bijSq (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀) (𝒱 : Set X.Opens) (h : St Q₀ 𝒱 ≤ Q')
    (h' : Q' ≤ St Q₀ {sSup 𝒱}) (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T')
    (a b : IdF (sP Q').A) (ha : LocI a) (hb : LocI b) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (sq a b) (ObjectProperty.ιOfLE h)).pull j) :=
  bij_restrict h _ (zarCov Q₀ hQ 𝒱 h' hc _ fun T _ f hf hq => ⟨locSq a b ha hb T f hf hq⟩) j

theorem bijO (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀) (𝒱 : Set X.Opens) (h : St Q₀ 𝒱 ≤ Q')
    (h' : Q' ≤ St Q₀ {sSup 𝒱}) (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (CH.modF (sP Q').A) (ObjectProperty.ιOfLE h)).pull j) :=
  bij_restrict h _ (zarCov Q₀ hQ 𝒱 h' hc _ fun T _ f hf hq => ⟨locO T f hf hq⟩) j

theorem eq_fil {Q₁ : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q₁ ≤ Q') (r r' : ℤ) :
    (incl h).sq (incl_fil h r) (incl_fil h r') =
      CH.Mor.restrict (sq (sFil Q' r) (sFil Q' r')) (ObjectProperty.ιOfLE h) := by
  refine mor_eq (ObjectProperty.ιOfLE h) _ _ rfl rfl fun T x => ?_
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem eq_o {Q₁ : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q₁ ≤ Q') :
    (incl h).o = CH.Mor.restrict (CH.modF (sP Q').A) (ObjectProperty.ιOfLE h) :=
  mor_eq (ObjectProperty.ιOfLE h) _ _ rfl rfl fun T x => rfl

theorem bij_std (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀) (𝒱 : Set X.Opens) (h : St Q₀ 𝒱 ≤ Q')
    (h' : Q' ≤ St Q₀ {sSup 𝒱}) (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T')
    (r r' : Option ℤ) (c c' : R) (j : ℕ) :
    Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j) := by
  have hb := bijSq Q₀ hQ 𝒱 h h' hc (stdI Q' r c) (stdI Q' r' c') (locI_std r c) (locI_std r' c') j
  cases r <;> cases r' <;>
  · refine bij_of_eq _ _ (mor_eq (ObjectProperty.ιOfLE h) _ _ rfl rfl fun T x => ?_) j hb
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end GlobalTheory.CompanionTheory.ZarCosieve

open GlobalTheory.CompanionTheory.ZarCosieve in

theorem GlobalTheory.CompanionTheory.ZarCosieve.main : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  intro O R _ _ I γ p X q κ Q₀ hQ 𝒱 Q' h h' hc j
  refine ⟨fun r r' => ?_, fun r r' c c' => ?_, ?_⟩
  · exact bij_of_eq _ _ (eq_fil h r r') j (bijSq Q₀ hQ 𝒱 h h' hc _ _ (locI_fil r) (locI_fil r') j)
  · exact bij_std Q₀ hQ 𝒱 h h' hc r r' c c' j
  · exact bij_of_eq _ _ (eq_o h) j (bijO Q₀ hQ 𝒱 h h' hc j)
