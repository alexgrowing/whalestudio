import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NlZar

section Gen
universe w v u
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

structure RAct (A : C ⥤ CommAlgCat.{0} R) (F : C ⥤ ModuleCat.{w} R) where
  ρ : ∀ T : C, A.obj T →+* Module.End R (F.obj T)
  nat : ∀ {T T' : C} (φ : T ⟶ T') (c : A.obj T) (x : F.obj T),
    (F.map φ).hom (ρ T c x) = ρ T' ((A.map φ).hom c) ((F.map φ).hom x)

def RAct.locMod {A : C ⥤ CommAlgCat.{0} R} {F : C ⥤ ModuleCat.{w} R} (P : RAct A F) (T' : C) {m : ℕ}
    (f : Fin m → A.obj T') (hf : Ideal.span (Set.range f) = ⊤) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (hu : ∀ S, ∀ k ∈ S, IsUnit ((A.map (lam S)).hom (f k)))
    (hs : ∀ S (y : F.obj (Lc S)), ∃ (n : ℕ) (x : F.obj T'),
      P.ρ _ ((A.map (lam S)).hom ((∏ k ∈ S, f k) ^ n)) y = (F.map (lam S)).hom x)
    (hk : ∀ S (x : F.obj T'), (F.map (lam S)).hom x = 0 → ∃ n : ℕ, P.ρ T' ((∏ k ∈ S, f k) ^ n) x = 0) :
    CrystallineSemistableComparison.B.LocMod F T' Lc lam where
  Λ := A.obj T'
  ring := inferInstance
  f := f
  span := hf
  ρ₀ := P.ρ T'
  ρ S := (P.ρ (Lc S)).comp (A.map (lam S)).hom.toRingHom
  lam_ρ S a x := P.nat _ a x
  tr_ρ S S' t ht a x := by
    have e : (A.map t).hom ((A.map (lam S)).hom a) = (A.map (lam S')).hom a := by
      rw [← ht, A.map_comp]; rfl
    exact (P.nat t _ x).trans (congrArg (fun c => P.ρ _ c ((F.map t).hom x)) e)
  unit S k hk' := by
    obtain ⟨u, hu'⟩ := hu S k hk'
    have h1 : ∀ y, P.ρ (Lc S) (↑u : A.obj (Lc S)) (P.ρ (Lc S) (↑u⁻¹ : A.obj (Lc S)) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
    have h2 : ∀ y, P.ρ (Lc S) (↑u⁻¹ : A.obj (Lc S)) (P.ρ (Lc S) (↑u : A.obj (Lc S)) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    change Function.Bijective (P.ρ _ ((A.map (lam S)).hom (f k)))
    rw [← hu']
    exact ⟨Function.LeftInverse.injective h2, Function.RightInverse.surjective h1⟩
  surj := hs
  ker := hk

variable {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (c : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ c * x.1, Ideal.mul_mem_left _ _ x.2⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' r x := Subtype.ext (mul_smul_comm r _ _)

def sqAct (a b : IdF A) : RAct A (sq a b) where
  ρ T :=
    { toFun := mulSq a b T
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        change Ideal.Quotient.mk _ 1 * x.1 = x.1
        rw [map_one, one_mul])
      map_mul' := fun c c' => LinearMap.ext fun x => Subtype.ext (by
        change Ideal.Quotient.mk _ (c * c') * x.1 = Ideal.Quotient.mk _ c * (Ideal.Quotient.mk _ c' * x.1)
        rw [map_mul, mul_assoc])
      map_zero' := LinearMap.ext fun x => Subtype.ext (by
        change Ideal.Quotient.mk _ 0 * x.1 = 0
        rw [map_zero, zero_mul])
      map_add' := fun c c' => LinearMap.ext fun x => Subtype.ext (by
        change Ideal.Quotient.mk _ (c + c') * x.1 = Ideal.Quotient.mk _ c * x.1 + Ideal.Quotient.mk _ c' * x.1
        rw [map_add, add_mul]) }
  nat {T T'} φ c x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    change Ideal.Quotient.mk _ ((A.map φ).hom (c * y)) =
      Ideal.Quotient.mk _ ((A.map φ).hom c) * Ideal.Quotient.mk _ ((A.map φ).hom y)
    rw [map_mul, map_mul]

def modAct (A : C ⥤ CommAlgCat.{0} R) : RAct A (CH.modF A) where
  ρ T := (Algebra.lmul R (A.obj T)).toRingHom
  nat φ c x := map_mul (A.map φ).hom c x

theorem sq_surj (a b : IdF A) {T' L : C} (l : T' ⟶ L) (d : A.obj T')
    (h : ∀ y ∈ a.S L, ∃ (n : ℕ), ∃ x ∈ a.S T', (A.map l).hom (d ^ n) * y = (A.map l).hom x)
    (y : (sq a b).obj L) : ∃ (n : ℕ) (x : (sq a b).obj T'),
      (sqAct a b).ρ _ ((A.map l).hom (d ^ n)) y = ((sq a b).map l).hom x := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  obtain ⟨n, x, hx, e⟩ := h z hz
  refine ⟨n, sqMk a b x hx, Subtype.ext ?_⟩
  change Ideal.Quotient.mk _ ((A.map l).hom (d ^ n)) * Ideal.Quotient.mk _ z = Ideal.Quotient.mk _ ((A.map l).hom x)
  rw [← map_mul, e]

theorem sq_ker (a b : IdF A) {T' L : C} (l : T' ⟶ L) (d : A.obj T')
    (h : ∀ x, (A.map l).hom x ∈ b.S L → ∃ n : ℕ, d ^ n * x ∈ b.S T')
    (x : (sq a b).obj T') (hx : ((sq a b).map l).hom x = 0) :
    ∃ n : ℕ, (sqAct a b).ρ T' (d ^ n) x = 0 := by
  obtain ⟨x, hx'⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h0 : Ideal.Quotient.mk (b.S L) ((A.map l).hom y) = 0 := congrArg Subtype.val hx
  obtain ⟨n, hn⟩ := h y (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  refine ⟨n, Subtype.ext ?_⟩
  change Ideal.Quotient.mk _ (d ^ n) * Ideal.Quotient.mk _ y = 0
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hn

end Gen

section Cover

theorem exists_cover {A : Type} [CommRing A] {X : Scheme.{0}} (y : Spec (CommRingCat.of A) ⟶ X) (𝒱 : Set X.Opens)
    (h : ∀ x, ∃ V ∈ 𝒱, y x ∈ V) :
    ∃ (m : ℕ) (s : Fin m → A), Ideal.span (Set.range s) = ⊤ ∧ ∀ k, ∃ V ∈ 𝒱, ∀ (A' : Type) [CommRing A'] (g : A →+* A'),
      IsUnit (g (s k)) → ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ y) ⁻¹ᵁ V := by
  have h1 : ∀ x : PrimeSpectrum A, ∃ (V : X.Opens) (c : A), V ∈ 𝒱 ∧ x ∈ PrimeSpectrum.basicOpen c ∧
      ∀ z : PrimeSpectrum A, z ∈ PrimeSpectrum.basicOpen c → y z ∈ V := by
    intro x
    obtain ⟨V, hV, hx⟩ := h x
    let U : Set (PrimeSpectrum A) := (y ⁻¹ᵁ V).1
    have hU : IsOpen U := (y ⁻¹ᵁ V).2
    have hxU : x ∈ U := hx
    obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
    exact ⟨V, c, hV, hc, fun z hz => hsub hz⟩
  choose V c hV hx hsub using h1
  have hspan : Ideal.span (Set.range c) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have := hx ⟨M, hM.isPrime⟩
    exact this (hle (Ideal.subset_span ⟨_, rfl⟩))
  obtain ⟨s', hs', hs⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  refine ⟨s'.card, fun k => (s'.equivFin.symm k).1, ?_, fun k => ?_⟩
  · rw [← hs]
    congr 1
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact (s'.equivFin.symm k).2
    · intro ha
      exact ⟨s'.equivFin ⟨a, ha⟩, by simp⟩
  · obtain ⟨x, hxk⟩ := hs' (s'.equivFin.symm k).2
    refine ⟨V x, hV x, fun A' _ g hu z _ => ?_⟩
    refine hsub x (PrimeSpectrum.comap g z) ?_
    rw [hxk]
    intro hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

end Cover

section Th
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def locN (T : Thick (nlFun γ p X q κ)) (a : T.B) : Thick (nlFun γ p X q κ) :=
  GlobalTheory.CompanionTheory.ThickZar.locT (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T a

def locNHom (T : Thick (nlFun γ p X q κ)) (a : T.B) : T ⟶ locN T a :=
  GlobalTheory.CompanionTheory.ThickZar.locHom (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T a

theorem locNHom_φ (T : Thick (nlFun γ p X q κ)) (a : T.B) :
    (locNHom T a).φ = algebraMap T.B (Localization.Away a) := rfl

theorem locN_i (T : Thick (nlFun γ p X q κ)) (a : T.B) :
    (locN T a).i = (algebraMap T.B (Localization.Away a)).comp T.i := rfl

theorem locN_univ (T : Thick (nlFun γ p X q κ)) (a : T.B) {T'' : Thick (nlFun γ p X q κ)} (ψ : T ⟶ T'')
    (hu : IsUnit (ψ.φ a)) : ∃! χ : locN T a ⟶ T'', locNHom T a ≫ χ = ψ :=
  GlobalTheory.CompanionTheory.ThickZar.locT_univ (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T a ψ hu

theorem pdPow_locN (T : Thick (nlFun γ p X q κ)) (a : T.B) (r : ℕ) :
    (locN T a).pdPow r = (T.pdPow r).map (algebraMap T.B (Localization.Away a)) :=
  GlobalTheory.CompanionTheory.ThickZar.pdPow_locT (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T a r

theorem tf_loc {B : Type} [CommRing B] (a : B) (J : Ideal B) (l : ℕ) (hJ : ∀ x : B, (l : B) * x ∈ J → x ∈ J)
    (x : Localization.Away a) (hx : (l : Localization.Away a) * x ∈ J.map (algebraMap B (Localization.Away a))) :
    x ∈ J.map (algebraMap B (Localization.Away a)) := by
  obtain ⟨n, y, e⟩ := IsLocalization.Away.surj a x
  have hu : IsUnit (algebraMap B (Localization.Away a) a ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit a).pow n
  have h1 : algebraMap B (Localization.Away a) ((l : B) * y) ∈ J.map (algebraMap B (Localization.Away a)) := by
    have e2 : algebraMap B (Localization.Away a) ((l : B) * y) =
        algebraMap B (Localization.Away a) a ^ n * ((l : Localization.Away a) * x) := by
      rw [map_mul, ← e, map_natCast]; ring
    rw [e2]
    exact Ideal.mul_mem_left _ _ hx
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers a) _ _ _).1 h1
  have h2 : a ^ k * y ∈ J := hJ _ (by
    have e3 : (l : B) * (a ^ k * y) = a ^ k * ((l : B) * y) := by ring
    rw [e3]; exact hk)
  have h3 : algebraMap B (Localization.Away a) (a ^ k * y) ∈ J.map (algebraMap B (Localization.Away a)) :=
    Ideal.mem_map_of_mem _ h2
  have hu2 : IsUnit (algebraMap B (Localization.Away a) a ^ k * algebraMap B (Localization.Away a) a ^ n) :=
    ((IsLocalization.Away.algebraMap_isUnit a).pow k).mul hu
  have e4 : algebraMap B (Localization.Away a) (a ^ k * y) =
      (algebraMap B (Localization.Away a) a ^ k * algebraMap B (Localization.Away a) a ^ n) * x := by
    rw [map_mul, map_pow, ← e]; ring
  rw [e4] at h3
  exact (Ideal.unit_mul_mem_iff_mem _ hu2).1 h3

theorem used_locN {Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))} (hQ : Used Q₀) (T : Thick (nlFun γ p X q κ))
    (a : T.B) (h : Q₀ T) : Q₀ (locN T a) := by
  rcases hQ with ⟨-, l, s, rfl⟩ | ⟨-, rfl | rfl⟩
  · refine ⟨by rw [pdPow_locN, h.1, Ideal.map_bot], fun r x hx => ?_⟩
    rw [pdPow_locN] at hx ⊢
    exact tf_loc a _ l (h.2 r) x hx
  · trivial
  · change ((algebraMap T.B (Localization.Away a)).comp T.i).Flat
    have h1 : (algebraMap T.B (Localization.Away a)).Flat :=
      (RingHom.flat_algebraMap_iff).2 (IsLocalization.flat (Localization.Away a) (Submonoid.powers a))
    exact RingHom.Flat.comp h h1

theorem isNilpotent_of_mem_J (T : Thick (nlFun γ p X q κ)) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact this
  · exact GlobalTheory.CompanionTheory.ThickZar.isNilpotent_of_mem_J (b := nlBase R I γ p) hp T hx

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
    have := (isNilpotent_of_mem_J T hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

theorem pt_hom {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') :
    pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

end Th

section Cov
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def locO {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), Q T → Q (locN T a))
    (T : Q.FullSubcategory) (a : T.obj.B) : Q.FullSubcategory := ⟨locN T.obj a, hl _ _ T.property⟩

def locOHom {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), Q T → Q (locN T a))
    (T : Q.FullSubcategory) (a : T.obj.B) : T ⟶ locO hl T a := ObjectProperty.homMk (locNHom T.obj a)

theorem zarCov_of {Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))} (𝒱 𝒲 : Set X.Opens) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱)
    (hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), St Q₀ 𝒲 T → St Q₀ 𝒲 (locN T a))
    (F : (St Q₀ 𝒲).FullSubcategory ⥤ ModuleCat.{0} R)
    (hF : ∀ (T' : (St Q₀ 𝒲).FullSubcategory) {m : ℕ} (f : Fin m → T'.obj.B), Ideal.span (Set.range f) = ⊤ →
      Nonempty (CrystallineSemistableComparison.B.LocMod F T' (fun S => locO hl T' (∏ k ∈ S, f k)) (fun S => locOHom hl T' (∏ k ∈ S, f k)))) :
    CrystallineSemistableComparison.B.ZarCov F (fun T => St Q₀ 𝒱 T.obj) := by
  refine ⟨fun T T' φ hT => ?_, fun T => ?_⟩
  · obtain ⟨-, V, hV, hU⟩ := hT
    exact ⟨T'.property.1, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ.hom hU⟩
  obtain ⟨-, W, hW, hTW⟩ := T.property
  have hpt : ∀ x, ∃ V ∈ 𝒱, pt T.obj x ∈ V := fun x => by
    have h1 : pt T.obj x ∈ W := hTW (show x ∈ (⊤ : (Spec (CommRingCat.of (T.obj.B ⧸ T.obj.J))).Opens) from trivial)
    exact (TopologicalSpace.Opens.mem_sSup).1 (hc W hW h1)
  obtain ⟨m, s, hs, hcov⟩ := exists_cover (pt T.obj) 𝒱 hpt
  choose f hf using fun k => Ideal.Quotient.mk_surjective (s k)
  have hspan : Ideal.span (Set.range f) = ⊤ := span_lift T.obj f s hf hs
  refine ⟨m, fun k _ ψ => IsUnit (ψ.hom.φ (f k)), fun k T₁ T₂ ψ χ h => h.map χ.hom.φ, fun k T₁ ψ h => ?_, fun T' φ => ?_⟩
  · obtain ⟨V, hV, hVk⟩ := hcov k
    refine ⟨T₁.property.1, V, hV, ?_⟩
    have hu : IsUnit (Ideal.quotientMap T₁.obj.J ψ.hom.φ ψ.hom.hle (s k)) := by
      rw [← hf k]; exact h.map (Ideal.Quotient.mk T₁.obj.J)
    have h2 := hVk _ _ hu
    unfold InU
    rw [pt_hom ψ.hom]
    exact h2
  have hg : Ideal.span (Set.range fun k => φ.hom.φ (f k)) = ⊤ := by
    have h := congrArg (Ideal.map φ.hom.φ) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨hM⟩ := hF T' (fun k => φ.hom.φ (f k)) hg
  refine ⟨fun S => locO hl T' (∏ k ∈ S, φ.hom.φ (f k)), fun S => locOHom hl T' _, fun S k hk => ?_, fun S T'' ψ h => ?_, ⟨hM⟩⟩
  · exact GlobalTheory.CompanionTheory.ThickZar.unit_of_mem (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T'.obj
      (fun k => φ.hom.φ (f k)) S hk
  · have hu : IsUnit (ψ.hom.φ (∏ k ∈ S, φ.hom.φ (f k))) := by
      rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one h
    obtain ⟨χ, hχ, hχu⟩ := locN_univ T'.obj _ ψ.hom hu
    refine ⟨ObjectProperty.homMk χ, ObjectProperty.hom_ext _ hχ, fun χ' h' => ObjectProperty.hom_ext _ (hχu χ'.hom ?_)⟩
    exact congrArg (fun t => t.hom) h'

def LocI {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), Q T → Q (locN T a))
    (a : IdF (sP Q).A) : Prop :=
  ∀ (T : Q.FullSubcategory) (d : T.obj.B),
    (a.S (locO hl T d) : Ideal (Localization.Away d)) = Ideal.map (algebraMap T.obj.B (Localization.Away d)) (a.S T : Ideal T.obj.B)

section
variable {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), Q T → Q (locN T a)}

theorem locI_fil (r : ℤ) : LocI hl (sFil Q r) := fun T d => pdPow_locN T.obj d r.toNat

theorem locI_bot : LocI hl (IdF.bot (sP Q).A) := fun T d => (Ideal.map_bot).symm

theorem locI_span (c : R) : LocI hl (IdF.span (sP Q).A c) := fun T d => by
  change Ideal.span {algebraMap T.obj.B (Localization.Away d) (T.obj.i c)} = Ideal.map _ (Ideal.span {T.obj.i c})
  rw [Ideal.map_span, Set.image_singleton]

theorem locI_sup {a b : IdF (sP Q).A} (ha : LocI hl a) (hb : LocI hl b) : LocI hl (a.sup b) := fun T d => by
  have e1 := ha T d
  have e2 := hb T d
  refine Eq.trans ?_ (Ideal.map_sup _ _ _).symm
  exact congrArg₂ (· ⊔ ·) e1 e2

theorem locI_std (r : Option ℤ) (c : R) : LocI hl (stdI Q r c) := by
  cases r
  · exact locI_sup locI_bot (locI_span c)
  · exact locI_sup (locI_fil _) (locI_span c)

theorem map_surj {B : Type} [CommRing B] (d : B) (J : Ideal B) (y : Localization.Away d)
    (hy : y ∈ J.map (algebraMap B (Localization.Away d))) :
    ∃ (n : ℕ), ∃ x ∈ J, algebraMap B (Localization.Away d) (d ^ n) * y = algebraMap B (Localization.Away d) x := by
  obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers d) _).1 hy
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, x.1, x.2, ?_⟩
  have hn' : d ^ n = s := hn
  rw [mul_comm, hn']
  exact hx

theorem map_ker {B : Type} [CommRing B] (d : B) (J : Ideal B) (x : B)
    (hx : algebraMap B (Localization.Away d) x ∈ J.map (algebraMap B (Localization.Away d))) :
    ∃ n : ℕ, d ^ n * x ∈ J := by
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d) _ _ _).1 hx
  exact ⟨n, hn⟩

theorem unit_locO (T' : Q.FullSubcategory) {m : ℕ} (f : Fin m → T'.obj.B) (S : Finset (Fin m)) (k : Fin m) (hk : k ∈ S) :
    IsUnit (((sP Q).A.map (locOHom hl T' (∏ k ∈ S, f k))).hom (f k)) :=
  GlobalTheory.CompanionTheory.ThickZar.unit_of_mem (F := CrystallineSemistableComparison.B.schFn q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) T'.obj f S hk

theorem locMod_sq {a b : IdF (sP Q).A} (ha : LocI hl a) (hb : LocI hl b) (T' : Q.FullSubcategory) {m : ℕ}
    (f : Fin m → T'.obj.B) (hf : Ideal.span (Set.range f) = ⊤) :
    Nonempty (CrystallineSemistableComparison.B.LocMod (sq a b) T' (fun S => locO hl T' (∏ k ∈ S, f k)) (fun S => locOHom hl T' (∏ k ∈ S, f k))) :=
  ⟨(sqAct a b).locMod T' f hf _ _ (fun S k hk => unit_locO T' f S k hk)
    (fun S y => sq_surj a b (locOHom hl T' (∏ k ∈ S, f k)) (∏ k ∈ S, f k)
      (fun y hy => map_surj (∏ k ∈ S, f k) (a.S T') y (by
        have e := ha T' (∏ k ∈ S, f k)
        exact e.le hy)) y)
    (fun S x hx => sq_ker a b (locOHom hl T' (∏ k ∈ S, f k)) (∏ k ∈ S, f k)
      (fun x hx => map_ker (∏ k ∈ S, f k) (b.S T') x (by
        have e := hb T' (∏ k ∈ S, f k)
        exact e.le hx)) x hx)⟩

theorem locMod_o (T' : Q.FullSubcategory) {m : ℕ} (f : Fin m → T'.obj.B) (hf : Ideal.span (Set.range f) = ⊤) :
    Nonempty (CrystallineSemistableComparison.B.LocMod (CH.modF (sP Q).A) T' (fun S => locO hl T' (∏ k ∈ S, f k))
      (fun S => locOHom hl T' (∏ k ∈ S, f k))) :=
  ⟨(modAct (sP Q).A).locMod T' f hf _ _ (fun S k hk => unit_locO T' f S k hk)
    (fun S y => by
      obtain ⟨n, x, -, e⟩ := map_surj (∏ k ∈ S, f k) (⊤ : Ideal T'.obj.B) y (by
        rw [Ideal.map_top]; trivial)
      exact ⟨n, x, e⟩)
    (fun S x hx => by
      let x' : T'.obj.B := x
      obtain ⟨n, hn⟩ := map_ker (∏ k ∈ S, f k) (⊥ : Ideal T'.obj.B) x' (by
        have h0 : algebraMap T'.obj.B (Localization.Away (∏ k ∈ S, f k)) x' = 0 := hx
        rw [h0]; exact Ideal.zero_mem _)
      have hz : (∏ k ∈ S, f k) ^ n * x' = 0 := (Ideal.mem_bot).1 hn
      exact ⟨n, hz⟩)⟩

end

end Cov

section Main
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem bij_of_upTo {A : Type} [CommRing A] {M : Type*} {N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Module A N] (f : M →ₗ[A] N) (h : UpTo (1 : A) f) : Function.Bijective f := by
  refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
  · simpa using h.1 x hx
  · obtain ⟨x, hx⟩ := h.2 y
    exact ⟨x, by simpa using hx⟩

theorem onto_incl {Q Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q' ≤ Q) :
    CrystallineSemistableComparison.B.Onto (ObjectProperty.ιOfLE h) (fun T : Q.FullSubcategory => Q' T.obj) where
  full := inferInstance
  faithful := inferInstance
  mem T := T.property
  ess T hT := ⟨⟨T.obj, hT⟩, ⟨Iso.refl _⟩⟩

theorem sq_eq_restrict {Q Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q' ≤ Q) (a b : IdF (sP Q).A)
    (ha : (incl h).Le a (a.res (ObjectProperty.ιOfLE h) : IdF (sP Q').A))
    (hb : (incl h).Le b (b.res (ObjectProperty.ιOfLE h) : IdF (sP Q').A)) :
    (incl h).sq ha hb = CrystallineSemistableComparison.CH.Mor.restrict (sq a b) (ObjectProperty.ιOfLE h) := by
  have e : ((incl h).sq ha hb).τ = (CrystallineSemistableComparison.CH.Mor.restrict (sq a b) (ObjectProperty.ιOfLE h)).τ := by
    funext T
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  change CrystallineSemistableComparison.CH.Mor.mk _ _ _ = CrystallineSemistableComparison.CH.Mor.mk _ _ _
  congr

theorem bij_sq_of {Q Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q' ≤ Q) (a b : IdF (sP Q).A) (a' b' : IdF (sP Q').A)
    (ea : a' = (a.res (ObjectProperty.ιOfLE h) : IdF (sP Q').A)) (eb : b' = (b.res (ObjectProperty.ιOfLE h) : IdF (sP Q').A))
    (ha : (incl h).Le a a') (hb : (incl h).Le b b') (j : ℕ)
    (hB : Function.Bijective ((CrystallineSemistableComparison.CH.Mor.restrict (sq a b) (ObjectProperty.ιOfLE h)).pull j)) :
    Function.Bijective (((incl h).sq ha hb).pull j) := by
  subst ea eb
  rw [sq_eq_restrict]
  exact hB

theorem std_res {Q Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (h : Q' ≤ Q) (r : Option ℤ) (c : R) :
    stdI Q' r c = ((stdI Q r c).res (ObjectProperty.ιOfLE h) : IdF (sP Q').A) := by
  cases r <;> rfl

end Main

theorem zariski_descent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 𝒲 : Set X.Opens) (h : St Q₀ 𝒱 ≤ St Q₀ 𝒲) (hc : ∀ W ∈ 𝒲, W ≤ sSup 𝒱) (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  intro O R _ _ I γ p X q κ Q₀ hQ 𝒱 𝒲 h hc j
  have hl : ∀ (T : Thick (nlFun γ p X q κ)) (a : T.B), St Q₀ 𝒲 T → St Q₀ 𝒲 (locN T a) := fun T a hT => by
    obtain ⟨h0, W, hW, hU⟩ := hT
    exact ⟨used_locN hQ T a h0, W, hW, GlobalTheory.CompanionTheory.ThickPt.inU_map W (locNHom T a) hU⟩
  have key : ∀ (F : (St Q₀ 𝒲).FullSubcategory ⥤ ModuleCat.{0} R),
      (∀ (T' : (St Q₀ 𝒲).FullSubcategory) {m : ℕ} (f : Fin m → T'.obj.B), Ideal.span (Set.range f) = ⊤ →
        Nonempty (CrystallineSemistableComparison.B.LocMod F T' (fun S => locO hl T' (∏ k ∈ S, f k)) (fun S => locOHom hl T' (∏ k ∈ S, f k)))) →
      Function.Bijective ((CrystallineSemistableComparison.CH.Mor.restrict F (ObjectProperty.ιOfLE h)).pull j) := fun F hF =>
    bij_of_upTo _ (CrystallineSemistableComparison.B.P.zar F _ (ObjectProperty.ιOfLE h) (onto_incl h) (zarCov_of 𝒱 𝒲 hc hl F hF) j j le_rfl)
  refine ⟨fun r r' => ?_, fun r r' c c' => ?_, ?_⟩
  · exact bij_sq_of h _ _ _ _ rfl rfl _ _ j (key _ fun T' _ f hf => locMod_sq (locI_fil r) (locI_fil r') T' f hf)
  · exact bij_sq_of h (stdI _ r c) (stdI _ r' c') _ _ (std_res h r c) (std_res h r' c') _ _ j
      (key _ fun T' _ f hf => locMod_sq (locI_std r c) (locI_std r' c') T' f hf)
  · exact key (CH.modF (sP (St Q₀ 𝒲)).A) fun T' _ f hf => locMod_o T' f hf

end GlobalTheory.CompanionTheory.NlZar
