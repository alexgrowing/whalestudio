import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnFibresFlatBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem exists_opens_preimage_le_of_isClosedMap {F Y : Scheme.{0}} (φ : F ⟶ Y) (hφ : IsClosedMap φ) (y : Y)
    (T : F.Opens) (hT : ∀ p, φ p = y → p ∈ T) : ∃ N : Y.Opens, y ∈ N ∧ φ ⁻¹ᵁ N ≤ T := by
  refine ⟨⟨(φ '' (T : Set F)ᶜ)ᶜ, (hφ _ T.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, e⟩
    exact hp (hT p e)
  · intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩

theorem exists_basicOpen_le_of_finite {A : Type} [CommRing A] (s : Set (PrimeSpectrum A)) (hs : s.Finite)
    (U : Set (PrimeSpectrum A)) (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ b : A, s ⊆ PrimeSpectrum.basicOpen b ∧ (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  by_cases hne : s = ∅
  · subst hne
    exact ⟨0, by simp, by simp⟩
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hne
  have key : ¬ ((I : Set A) ⊆ ⋃ i ∈ s, (i.asIdeal : Set A)) := by
    rw [Ideal.subset_union_prime_finite hs a a (fun i _ _ _ => i.2)]
    rintro ⟨i, hi, hle⟩
    have : i ∈ Uᶜ := by rw [hI]; exact hle
    exact this (hsU hi)
  obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 key
  refine ⟨b, fun i hi h => hb' (Set.mem_iUnion₂.2 ⟨i, hi, h⟩), fun i hi => ?_⟩
  by_contra h
  have : i ∈ PrimeSpectrum.zeroLocus (I : Set A) := hI ▸ h
  exact hi (this hb)

theorem exists_basicOpen_le_of_finite' {G : Scheme.{0}} {W : G.Opens} (hW : IsAffineOpen W) (s : Set G) (hs : s.Finite)
    (hsW : s ⊆ W) (U : G.Opens) (hsU : s ⊆ U) : ∃ b : Γ(G, W), s ⊆ G.basicOpen b ∧ G.basicOpen b ≤ U := by
  obtain ⟨b, h₁, h₂⟩ := exists_basicOpen_le_of_finite (A := Γ(G, W)) (hW.fromSpec ⁻¹' s)
    (hs.preimage hW.fromSpec.isOpenEmbedding.injective.injOn) _
    (hW.fromSpec ⁻¹ᵁ U).2 (fun p hp => hsU hp)
  refine ⟨b, fun p hp => ?_, ?_⟩
  · have : p ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hsW hp
    obtain ⟨q, rfl⟩ := this
    rw [← hW.fromSpec_image_basicOpen]
    exact ⟨q, h₁ hp, rfl⟩
  · rw [← hW.fromSpec_image_basicOpen]
    rintro _ ⟨q, hq, rfl⟩
    exact h₂ hq

theorem exists_affine_preimage_eq_basicOpen {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {W : G.Opens} (hW : IsAffineOpen W) (y : Y) (hfin : (κ '' {p | φ p = y}).Finite)
    (hy : ∀ p, φ p = y → κ p ∈ W) :
    ∃ (O : Y.Opens) (b : Γ(G, W)), y ∈ O ∧ IsAffineOpen O ∧ φ ⁻¹ᵁ O = κ ⁻¹ᵁ G.basicOpen b := by
  obtain ⟨N, hyN, hN⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ W) hy
  obtain ⟨_, ⟨O₁, hO₁, rfl⟩, hyO₁, hO₁N⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyN N.2
  let U : G.Opens := ⟨(κ '' ((φ ⁻¹ᵁ O₁ : F.Opens) : Set F)ᶜ)ᶜ,
    (κ.isClosedEmbedding.isClosedMap _ (φ ⁻¹ᵁ O₁).2.isClosed_compl).isOpen_compl⟩
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_basicOpen_le_of_finite' hW _ hfin (by rintro _ ⟨p, hp, rfl⟩; exact hy p hp) U (by
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, e⟩
    obtain rfl := κ.isClosedEmbedding.injective e
    apply hq
    change φ q ∈ O₁
    rw [hp]; exact hyO₁)
  have hle : κ ⁻¹ᵁ G.basicOpen b₁ ≤ φ ⁻¹ᵁ O₁ := fun p hp => by
    by_contra h
    exact hb₁' hp ⟨p, h, rfl⟩
  obtain ⟨N₂, hyN₂, hN₂⟩ := exists_opens_preimage_le_of_isClosedMap φ hφ y (κ ⁻¹ᵁ G.basicOpen b₁)
    (fun p hp => hb₁ ⟨p, hp, rfl⟩)
  obtain ⟨g, hg, hyg⟩ := IsAffineOpen.exists_basicOpen_le hO₁ (V := N₂) ⟨y, hyN₂⟩ hyO₁
  have hS : IsAffineOpen (κ ⁻¹ᵁ W) := hW.preimage κ
  rw [Scheme.preimage_basicOpen] at hle hN₂
  obtain ⟨s, hs⟩ := hS.basicOpen_basicOpen_is_basicOpen (κ.app W b₁) (φ.appLE O₁ _ hle g)
  obtain ⟨b, rfl⟩ := κ.app_surjective W hW s
  refine ⟨Y.basicOpen g, b, hyg, hO₁.basicOpen g, ?_⟩
  rw [Scheme.preimage_basicOpen κ, hs, Scheme.basicOpen_appLE, eq_comm, inf_eq_right]
  exact fun p hp => hN₂ (hg hp)

theorem exists_affine_preimage_iff_not_mem {F G Y : Scheme.{0}} (κ : F ⟶ G) [IsClosedImmersion κ] (φ : F ⟶ Y)
    (hφ : IsClosedMap φ) {A : Type} [CommRing A] (J : Sp A ⟶ G) [IsOpenImmersion J] (y : Y)
    (hfin : (κ '' {p | φ p = y}).Finite) (hy : ∀ p, φ p = y → κ p ∈ Set.range J) :
    ∃ (O : Y.Opens) (b : A), y ∈ O ∧ IsAffineOpen O ∧
      ∀ p, φ p ∈ O ↔ ∃ q : PrimeSpectrum A, J q = κ p ∧ b ∉ q.asIdeal := by
  obtain ⟨O, b, h₁, h₂, h₃⟩ := exists_affine_preimage_eq_basicOpen κ φ hφ (isAffineOpen_opensRange J) y hfin hy
  have e : (⊤ : (Sp A).Opens) ≤ J ⁻¹ᵁ J.opensRange := fun q _ => ⟨q, rfl⟩
  refine ⟨O, (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b), h₁, h₂, fun p => ?_⟩
  have h₄ := basicOpen_eq_of_affine' (R := .of A) (J.appLE _ _ e b)
  rw [Scheme.basicOpen_appLE, top_inf_eq] at h₄
  have h₅ : ∀ q : PrimeSpectrum A, J q ∈ G.basicOpen b ↔
      (Scheme.ΓSpecIso (.of A)).hom (J.appLE _ _ e b) ∉ q.asIdeal := fun q => by
    change q ∈ J ⁻¹ᵁ G.basicOpen b ↔ _
    rw [h₄]; rfl
  change p ∈ φ ⁻¹ᵁ O ↔ _
  rw [h₃]
  change κ p ∈ G.basicOpen b ↔ _
  constructor
  · intro h
    obtain ⟨q, hq⟩ := G.basicOpen_le b h
    exact ⟨q, hq, (h₅ q).1 (by rw [hq]; exact h)⟩
  · rintro ⟨q, hq, h⟩
    rw [← hq]; exact (h₅ q).2 h

theorem exists_act_eq_of_apply_eq {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (hG : IsGal (algebraMap R R')) {F G T : Scheme.{0}} (t : T ⟶ Sp R')
    [IsClosedImmersion t] (κ : F ⟶ G) (gm : G ⟶ Sp R') (s : F ⟶ T) (hs : κ ≫ gm = s ≫ t)
    (act : Gal (algebraMap R R') → (G ⟶ G)) (hact : ∀ σ, act σ ≫ gm = gm ≫ spMap (Gal.hom σ)) (Y : Over (Sp R))
    (hY : Flat Y.hom) (φ : F ⟶ Y.left) (hφ : IsPullback φ s Y.hom (t ≫ spMap (algebraMap R R')))
    (hinv : ∀ σ, ∃ h : F ⟶ F, h ≫ κ = κ ≫ act σ ∧ h ≫ φ = φ) (p q : F) (e : φ p = φ q) :
    ∃ σ, act σ (κ p) = κ q := by
  let u : F ⟶ pullback Y.hom (spMap (algebraMap R R')) := pullback.lift φ (s ≫ t) (by rw [hφ.w, Category.assoc])
  have hu₁ : u ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ pullback.snd _ _ = s ≫ t := pullback.lift_snd _ _ _
  have hu : IsPullback s u t (pullback.snd Y.hom (spMap (algebraMap R R'))) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst _ _) ?_ hu₂.symm (IsPullback.of_hasPullback _ _).flip
    rw [hu₁]; exact hφ.flip
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hu inferInstance
  obtain ⟨σ, h, h₁, h₂, h₃⟩ := GlobalTheory.T.galois_transitive_on_fibres_flat_baseChange R R' hinj hG Y hY _ _ _ (IsPullback.of_hasPullback _ _) (u p) (u q) (by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hu₁, e])
  obtain ⟨k, k₁, k₂⟩ := hinv σ
  have hk : k ≫ u = u ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, hu₁, k₂]
    · rw [Category.assoc, Category.assoc, h₂, hu₂, ← Category.assoc u, hu₂, ← hs, ← Category.assoc k, k₁, Category.assoc,
        hact, Category.assoc]
  have hkp : k p = q := u.isClosedEmbedding.injective (by
    rw [← h₃, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk])
  exact ⟨σ, by rw [← hkp, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, k₁]⟩

theorem mem_range_thick_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R')
    (hρ : ρ.Finite) (P : Sp R') (hP : spMap ρ P = closedPoint R) (e : ℕ) :
    P ∈ Set.range (thick R' (maximalIdeal R') e) := by
  have h₁ : (P.asIdeal.comap ρ).IsMaximal := by
    have : P.asIdeal.comap ρ = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hP
    rw [this]; infer_instance
  have := P.2
  have h₂ : P.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ h₁
  have h₃ : P.asIdeal = maximalIdeal R' := eq_maximalIdeal h₂
  change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal R' ^ (e + 1))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  intro a ha
  change a ∈ P.asIdeal
  rw [h₃]
  exact Ideal.pow_le_self (Nat.succ_ne_zero e) ha

theorem exists_affine_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (Y : Over (Sp R)) (φ : ∀ e : ℕ, (thickObj R' (maximalIdeal R') e G').left ⟶ Y.left), Smooth Y.hom → (∀ e, IsPullback (φ e) (thickObj R' (maximalIdeal R') e G').hom Y.hom (thick R' (maximalIdeal R') e ≫ spMap (algebraMap R R'))) → (∀ e, thickMap R' (maximalIdeal R') e G' ≫ φ (e + 1) = φ e) → (∀ e σ, ∃ h : (thickObj R' (maximalIdeal R') e G').left ⟶ (thickObj R' (maximalIdeal R') e G').left, h ≫ (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) = (pullback.fst G'.hom (thick R' (maximalIdeal R') e)) ≫ act σ ∧ h ≫ φ e = φ e) → ∀ x : H.toScheme, spMap (algebraMap R R') (G'.hom (H.ι x)) = closedPoint R → ∃ (V : X.left.Opens) (O : Y.left.Opens), π x ∈ V ∧ IsAffineOpen V ∧ IsAffineOpen O ∧ φ 0 ⁻¹ᵁ O = (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) ⁻¹ᵁ (H.ι ''ᵁ (π ⁻¹ᵁ V)) := by
  intro R _ _ _ R' _ _ _ _ hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec Y φ hY hφ _ hh x hx
  have := hG.1
  have := Fintype.ofFinite (Gal (algebraMap R R'))
  have hx₀ : H.ι x ∈ Set.range (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := by
    rw [Scheme.Pullback.range_fst]
    exact mem_range_thick_of_finite _ hF.2.2 _ hx 0
  obtain ⟨x₀, hx₀⟩ := hx₀
  have ht : IsClosedImmersion (thick R' (maximalIdeal R') 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hρ : IsFinite (spMap (algebraMap R R')) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hfin : IsFinite (φ 0) := MorphismProperty.of_isPullback (P := @IsFinite) (hφ 0).flip inferInstance
  have orb := exists_act_eq_of_apply_eq hF.2.1 hG (thick R' (maximalIdeal R') 0)
    (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) G'.hom _ pullback.condition act hact Y inferInstance (φ 0) (hφ 0) (hh 0)
  have hh₀ := hh 0
  have hκ : IsClosedImmersion (pullback.fst G'.hom (thick R' (maximalIdeal R') 0)) := inferInstance
  generalize pullback.fst G'.hom (thick R' (maximalIdeal R') 0) = κ at *
  obtain ⟨_, ⟨V₁, hV₁, rfl⟩, hxV₁, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π x)) isOpen_univ
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlr, hpb, -, -, hcomm, -, hC⟩ :=
    GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants R R' hB hF hG G' act hact h1 hmul H hH X π hπ haff hinv horb hsec V₁ hV₁
  have lift : ∀ (z : H.toScheme) (w : Sp C), π z = l w → ∃ q : Sp C', j q = z ∧ spMap (algebraMap C C') q = w :=
    fun z w e => Scheme.exists_preimage_of_isPullback hpb z w e
  have hw : ∀ q, π (j q) = l (spMap (algebraMap C C') q) := fun q => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have hc : ∀ σ q, (j ≫ H.ι) (spMap (actC σ : C' →+* C') q) = act σ ((j ≫ H.ι) q) := fun σ q => by
    rw [← Scheme.Hom.comp_apply, hcomm, ← Scheme.Hom.comp_apply, Category.assoc]
  obtain ⟨w₀, hw₀⟩ : π x ∈ Set.range l := by rw [hlr]; exact hxV₁
  obtain ⟨q₀, hq₀, -⟩ := lift x w₀ hw₀.symm
  have hq₀' : (j ≫ H.ι) q₀ = κ x₀ := by rw [Scheme.Hom.comp_apply, hq₀, hx₀]
  obtain ⟨O, b, hyO, hO, hb⟩ := exists_affine_preimage_iff_not_mem κ (φ 0) (φ 0).isClosedMap (j ≫ H.ι) (φ 0 x₀)
    ((Set.finite_range fun σ => act σ (κ x₀)).subset (by
      rintro _ ⟨p, hp, rfl⟩
      exact orb x₀ p hp.symm))
    (fun p hp => by
      obtain ⟨σ, hσ⟩ := orb x₀ p hp.symm
      exact ⟨_, (hc σ q₀).trans (by rw [hq₀', hσ])⟩)
  let c : C := ⟨∏ σ, actC σ b, (hC _).2 fun τ => by
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => by simp⟩
  have key : ∀ p, φ 0 p ∈ O ↔ ∃ q : PrimeSpectrum C', (j ≫ H.ι) q = κ p ∧ (c : C') ∉ q.asIdeal := fun p => by
    constructor
    · intro hp
      obtain ⟨q, hq, -⟩ := (hb p).1 hp
      refine ⟨q, hq, fun hm => ?_⟩
      obtain ⟨σ, -, hσ⟩ := (q.2.prod_mem_iff).1 hm
      obtain ⟨k, k₁, k₂⟩ := hh₀ σ
      obtain ⟨q', hq', hb'⟩ := (hb (k p)).1 (by rw [← Scheme.Hom.comp_apply, k₂]; exact hp)
      have : q' = spMap (actC σ : C' →+* C') q := (j ≫ H.ι).isOpenEmbedding.injective
        ((hq'.trans (by rw [hq, ← Scheme.Hom.comp_apply k κ, k₁, Scheme.Hom.comp_apply])).trans (hc σ q).symm)
      rw [this] at hb'
      exact hb' hσ
    · rintro ⟨q, hq, hm⟩
      refine (hb p).2 ⟨q, hq, fun hm' => hm ?_⟩
      exact (q.2.prod_mem_iff).2 ⟨1, Finset.mem_univ _, by simpa using hm'⟩
  have key₂ : ∀ z : H.toScheme, π z ∈ l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens) ↔
      ∃ q : PrimeSpectrum C', j q = z ∧ (c : C') ∉ q.asIdeal := fun z => by
    constructor
    · rintro ⟨w, hw', e⟩
      obtain ⟨q, hq, rfl⟩ := lift z w e.symm
      exact ⟨q, hq, hw'⟩
    · rintro ⟨q, rfl, hq⟩
      exact ⟨_, hq, (hw q).symm⟩
  refine ⟨l ''ᵁ (PrimeSpectrum.basicOpen c : (Sp C).Opens), O, ?_, ?_, hO, ?_⟩
  · obtain ⟨q, hq, hm⟩ := (key x₀).1 hyO
    refine (key₂ x).2 ⟨q, H.ι.isOpenEmbedding.injective ?_, hm⟩
    rw [← hx₀, ← hq]; exact (Scheme.Hom.comp_apply _ _ _).symm
  · refine IsAffineOpen.image_of_isOpenImmersion ?_ l
    rw [← basicOpen_eq_of_affine (R := .of C)]
    exact (isAffineOpen_top _).basicOpen _
  · ext p
    refine (key p).trans ⟨?_, ?_⟩
    · rintro ⟨q, hq, hm⟩
      exact ⟨j q, (key₂ _).2 ⟨q, rfl, hm⟩, hq⟩
    · rintro ⟨z, hz, e⟩
      obtain ⟨q, rfl, hm⟩ := (key₂ z).1 hz
      exact ⟨q, e, hm⟩

end GlobalTheory.Mum
