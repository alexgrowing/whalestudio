import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingKrullDimQuotientMvPolynomialEqNat

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

section FiniteSets

variable {X Y : Scheme.{u}}

private theorem mem_basicOpen_iff_not_mem_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (f : Γ(X, U)) : x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  change x ∈ X.basicOpen f ↔ hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f
  rw [hU.fromSpec_primeIdealOf]

theorem exists_basicOpen_le_of_finite {U : X.Opens} (hU : IsAffineOpen U) (O : X.Opens)
    {s : Set X} (hs : s.Finite) (hsU : s ⊆ U) (hsO : s ⊆ O) :
    ∃ f : Γ(X, U), s ⊆ X.basicOpen f ∧ X.basicOpen f ≤ O := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨0, Set.empty_subset _, by rw [Scheme.basicOpen_zero]; exact bot_le⟩
  have hloc : ∀ y : s, ∃ g : Γ(X, U), X.basicOpen g ≤ O ∧ (y : X) ∈ X.basicOpen g :=
    fun y ↦ hU.exists_basicOpen_le ⟨y, hsO y.2⟩ (hsU y.2)
  choose g hgO hyg using hloc
  let P : X → Ideal Γ(X, U) := fun y ↦ if h : y ∈ U then (hU.primeIdealOf ⟨y, h⟩).asIdeal else ⊤
  have hP : ∀ y (h : y ∈ U), P y = (hU.primeIdealOf ⟨y, h⟩).asIdeal := fun y h ↦ dif_pos h
  have hnot : ¬ ((Ideal.span (Set.range g) : Set Γ(X, U)) ⊆ ⋃ i ∈ (↑hs.toFinset : Set X), P i) := by
    rw [Ideal.subset_union_prime y₀ y₀ (fun i hi _ _ ↦ by
      rw [hP i (hsU (hs.mem_toFinset.1 hi))]; infer_instance)]
    rintro ⟨i, hi, hJ⟩
    have his : i ∈ s := hs.mem_toFinset.1 hi
    have h1 := hyg ⟨i, his⟩
    rw [mem_basicOpen_iff_not_mem_primeIdealOf hU (hsU his), ← hP] at h1
    exact h1 (hJ (Ideal.subset_span ⟨⟨i, his⟩, rfl⟩))
  rw [Set.not_subset] at hnot
  obtain ⟨f, hfJ, hf⟩ := hnot
  refine ⟨f, fun y hy ↦ ?_, fun z hz ↦ ?_⟩
  · rw [SetLike.mem_coe, mem_basicOpen_iff_not_mem_primeIdealOf hU (hsU hy), ← hP]
    exact fun h ↦ hf (Set.mem_biUnion (hs.mem_toFinset.2 hy) h)
  · have hz' : ¬ ∀ g' ∈ (Ideal.span (Set.range g) : Set Γ(X, U)), z ∉ X.basicOpen g' :=
      fun h ↦ h f hfJ hz
    rw [← Scheme.mem_zeroLocus_iff, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hz'
    push_neg at hz'
    obtain ⟨_, ⟨i, rfl⟩, hzi⟩ := hz'
    exact hgO i hzi

class FiniteSubsetsInAffineOpens (X : Scheme.{u}) : Prop where

  exists_isAffineOpen : ∀ s : Set X, s.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U

namespace FiniteSubsetsInAffineOpens

instance (priority := 900) of_isAffine [IsAffine X] : FiniteSubsetsInAffineOpens X :=
  ⟨fun _ _ ↦ ⟨⊤, isAffineOpen_top X, Set.subset_univ _⟩⟩

theorem exists_isAffineOpen_le [FiniteSubsetsInAffineOpens X] {s : Set X} (hs : s.Finite)
    (O : X.Opens) (hsO : s ⊆ O) : ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U ∧ U ≤ O := by
  obtain ⟨U, hU, hsU⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen s hs
  obtain ⟨f, hsf, hfO⟩ := exists_basicOpen_le_of_finite hU O hs hsU hsO
  exact ⟨X.basicOpen f, hU.basicOpen f, hsf, hfO⟩

theorem of_isAffineHom (f : X ⟶ Y) [IsAffineHom f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X := ⟨fun s hs ↦ by
  obtain ⟨V, hV, hsV⟩ := exists_isAffineOpen (X := Y) ((fun x : X ↦ f x) '' s) (hs.image _)
  exact ⟨f ⁻¹ᵁ V, hV.preimage f, fun x hx ↦ hsV ⟨x, hx, rfl⟩⟩⟩

theorem of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X := ⟨fun s hs ↦ by
  obtain ⟨V, hV, hsV, hVf⟩ := exists_isAffineOpen_le (X := Y) (hs.image (fun x : X ↦ f x))
    f.opensRange (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
  refine ⟨f ⁻¹ᵁ V, ?_, fun x hx ↦ hsV ⟨x, hx, rfl⟩⟩
  rw [← f.isAffineOpen_iff_of_isOpenImmersion, f.image_preimage_eq_opensRange_inf,
    inf_eq_right.2 hVf]
  exact hV⟩

instance opens [FiniteSubsetsInAffineOpens X] (U : X.Opens) : FiniteSubsetsInAffineOpens U :=
  of_isOpenImmersion U.ι

theorem of_isImmersion (f : X ⟶ Y) [IsImmersion f] [FiniteSubsetsInAffineOpens Y] :
    FiniteSubsetsInAffineOpens X :=
  of_isAffineHom (Y := f.coborderRange.toScheme) f.liftCoborder

theorem exists_proj_basicOpen {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {s : Set (Proj 𝒜)} (hs : s.Finite) :
    ∃ n, 0 < n ∧ ∃ f ∈ 𝒜 n, s ⊆ Proj.basicOpen 𝒜 f := by
  classical
  let S : Finset (Ideal A) := hs.toFinset.image (fun x : Proj 𝒜 ↦ x.asHomogeneousIdeal.toIdeal)
  have hmemS : ∀ p ∈ S, ∃ x : Proj 𝒜, p = x.asHomogeneousIdeal.toIdeal := by
    intro p hp
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨x, rfl⟩
  obtain ⟨n, hn, f, hf, hfM⟩ := exists_homogeneous_forall_notMem 𝒜
    (S.filter (fun p ↦ Maximal (· ∈ S) p))
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      exact x.isPrime)
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      exact x.asHomogeneousIdeal.isHomogeneous)
    (fun p hp q hq hqp ↦ (Finset.mem_filter.1 hq).2.eq_of_le (Finset.mem_filter.1 hp).1 hqp)
    (fun p hp ↦ by
      obtain ⟨x, rfl⟩ := hmemS p (Finset.mem_filter.1 hp).1
      obtain ⟨m, y, hy, hyI, hyp⟩ := exists_homogeneous_notMem_of_not_le 𝒜
        (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous (fun h ↦ x.not_irrelevant_le h)
      refine ⟨m, Nat.pos_of_ne_zero ?_, y, hy, hyp⟩
      rintro rfl
      have h0 := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 y).1 hyI
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hy] at h0
      exact hyp (by rw [h0]; exact Ideal.zero_mem _))
  refine ⟨n, hn, f, hf, fun x hx ↦ ?_⟩
  have hxS : x.asHomogeneousIdeal.toIdeal ∈ S := Finset.mem_image.2 ⟨x, hs.mem_toFinset.2 hx, rfl⟩
  obtain ⟨q, hxq, hq⟩ := S.exists_le_maximal hxS
  have hfq := hfM q (Finset.mem_filter.2 ⟨hq.prop, hq⟩)
  rw [SetLike.mem_coe, Proj.mem_basicOpen]
  exact fun h ↦ hfq (hxq h)

instance proj {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] : FiniteSubsetsInAffineOpens (Proj 𝒜) := ⟨fun _ hs ↦ by
  obtain ⟨n, hn, f, hf, hsf⟩ := exists_proj_basicOpen 𝒜 hs
  exact ⟨_, Proj.isAffineOpen_basicOpen 𝒜 f hf hn, hsf⟩⟩

theorem of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    FiniteSubsetsInAffineOpens X := by
  obtain ⟨N, i, hi, -, -⟩ := h
  exact of_isImmersion i

theorem of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) :
    FiniteSubsetsInAffineOpens X := by
  obtain ⟨N, i, hi, -⟩ := h
  exact of_isImmersion i

end FiniteSubsetsInAffineOpens

end FiniteSets

section Orbits

variable {G : Type v} [Group G] {X Y : Scheme.{u}}

class OrbitsInAffineOpens (ρ : G →* Aut X) : Prop where

  exists_isAffineOpen : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, (ρ g).hom x ∈ U

namespace OrbitsInAffineOpens

instance (priority := 900) of_finiteSubsetsInAffineOpens [Finite G] [FiniteSubsetsInAffineOpens X]
    (ρ : G →* Aut X) : OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨U, hU, h⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen _
    (Set.finite_range fun g ↦ (ρ g).hom x)
  exact ⟨U, hU, fun g ↦ h ⟨g, rfl⟩⟩⟩

theorem of_isQProjOver [Finite G] {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f)
    (ρ : G →* Aut X) : OrbitsInAffineOpens ρ := by
  have := FiniteSubsetsInAffineOpens.of_isQProjOver h
  infer_instance

theorem of_locally_on_base [Finite G] (ρ : G →* Aut X) (f : X ⟶ Y) (hf : ∀ g, (ρ g).hom ≫ f = f)
    (h : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ FiniteSubsetsInAffineOpens (f ⁻¹ᵁ W)) :
    OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨W, hyW, hW⟩ := h (f x)
  have horb : ∀ g, (ρ g).hom x ∈ f ⁻¹ᵁ W := fun g ↦ by
    show f ((ρ g).hom x) ∈ W
    rw [← Scheme.Hom.comp_apply, hf g]
    exact hyW
  obtain ⟨V, hV, hsV⟩ := FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := (f ⁻¹ᵁ W).toScheme)
    (Set.range fun g : G ↦ (⟨(ρ g).hom x, horb g⟩ : f ⁻¹ᵁ W)) (Set.finite_range _)
  refine ⟨(f ⁻¹ᵁ W).ι ''ᵁ V, hV.image_of_isOpenImmersion _, fun g ↦ ?_⟩
  exact ⟨_, hsV ⟨g, rfl⟩, rfl⟩⟩

theorem of_equivariant (ρ : G →* Aut X) (τ : G →* Aut Y) [OrbitsInAffineOpens τ] (p : X ⟶ Y)
    [IsAffineHom p] (hp : ∀ g, (ρ g).hom ≫ p = p ≫ (τ g).hom) : OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨V, hV, hxV⟩ := exists_isAffineOpen (ρ := τ) (p x)
  refine ⟨p ⁻¹ᵁ V, hV.preimage p, fun g ↦ ?_⟩
  show p ((ρ g).hom x) ∈ V
  rw [← Scheme.Hom.comp_apply, hp g, Scheme.Hom.comp_apply]
  exact hxV g⟩

theorem of_invariant (ρ : G →* Aut X) (p : X ⟶ Y) [IsAffineHom p]
    (hp : ∀ g, (ρ g).hom ≫ p = p) : OrbitsInAffineOpens ρ := ⟨fun x ↦ by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (p x))
  refine ⟨p ⁻¹ᵁ V, hV.preimage p, fun g ↦ ?_⟩
  show p ((ρ g).hom x) ∈ V
  rw [← Scheme.Hom.comp_apply, hp g]
  exact hxV⟩

instance comp {H : Type w} [Group H] (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] (φ : H →* G) :
    OrbitsInAffineOpens (ρ.comp φ) := ⟨fun x ↦ by
  obtain ⟨U, hU, h⟩ := exists_isAffineOpen (ρ := ρ) x
  exact ⟨U, hU, fun g ↦ h (φ g)⟩⟩

end OrbitsInAffineOpens

theorem IsAffineQuotient.orbitsInAffineOpens {ρ : G →* Aut X} {π : X ⟶ Y}
    (h : IsAffineQuotient ρ π) : OrbitsInAffineOpens ρ := by
  have := h.isAffineHom
  exact OrbitsInAffineOpens.of_invariant ρ π h.comp_eq

variable {ρ : G →* Aut X}

theorem aut_map_mul_apply (ρ : G →* Aut X) (g k : G) (x : X) :
    (ρ (g * k)).hom x = (ρ g).hom ((ρ k).hom x) := by
  rw [map_mul, Aut.Aut_mul_def]
  exact Scheme.Hom.comp_apply (ρ k).hom (ρ g).hom x

theorem aut_map_one_apply (ρ : G →* Aut X) (x : X) : (ρ 1).hom x = x := by
  rw [map_one]
  rfl

theorem IsInvariantSection.basicOpen_le {U : X.Opens} {s : Γ(X, U)}
    (hs : IsInvariantSection ρ U s) (g : G) : X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s := by
  obtain ⟨h, hgs⟩ := hs g
  have := Scheme.basicOpen_appLE (ρ g).hom U U h s
  rw [hgs] at this
  exact this.le.trans inf_le_right

private theorem mem_basicOpen_prod_iff {U : X.Opens} (a : G → Γ(X, U)) (T : Finset G) (x : X) :
    x ∈ X.basicOpen (∏ g ∈ T, a g) ↔ x ∈ U ∧ ∀ g ∈ T, x ∈ X.basicOpen (a g) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert g T hg ih =>
    rw [Finset.prod_insert hg, Scheme.basicOpen_mul, TopologicalSpace.Opens.mem_inf, ih,
      Finset.forall_mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩
      exact ⟨h1, h2, h3⟩

private theorem appLE_apply_congr' {f f' : X ⟶ X} (hff : f = f') (U : X.Opens) (e : U ≤ f ⁻¹ᵁ U)
    (e' : U ≤ f' ⁻¹ᵁ U) (s : Γ(X, U)) : f.appLE U U e s = f'.appLE U U e' s := by
  subst hff
  rfl

theorem exists_isInvariantSection_mem_basicOpen_iff [Finite G] {U : X.Opens}
    (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) (s : Γ(X, U)) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧
      ∀ x, x ∈ X.basicOpen t ↔ ∀ g, (ρ g).hom x ∈ X.basicOpen s := by
  classical
  have := Fintype.ofFinite G
  refine ⟨∏ g : G, (ρ g).hom.appLE U U (hU g) s, fun k ↦ ⟨hU k, ?_⟩, fun x ↦ ?_⟩
  · rw [map_prod]
    refine (Finset.prod_congr rfl fun g _ ↦ ?_).trans (Fintype.prod_equiv (Equiv.mulRight k)
      (fun g ↦ (ρ (g * k)).hom.appLE U U (hU (g * k)) s) _ (fun _ ↦ rfl))
    have e := Scheme.Hom.appLE_comp_appLE (ρ k).hom (ρ g).hom U U U (hU g) (hU k)
    have e' := congrArg (fun φ : Γ(X, U) ⟶ Γ(X, U) ↦ φ s) e
    simp only [CommRingCat.comp_apply] at e'
    rw [e']
    exact appLE_apply_congr' (by rw [map_mul, Aut.Aut_mul_def]; rfl) _ _ _ _
  · rw [mem_basicOpen_prod_iff]
    have key : ∀ g, x ∈ X.basicOpen ((ρ g).hom.appLE U U (hU g) s) ↔
        x ∈ U ∧ (ρ g).hom x ∈ X.basicOpen s := fun g ↦ by
      rw [Scheme.basicOpen_appLE]
      exact Iff.rfl
    simp only [Finset.mem_univ, true_implies, key]
    constructor
    · rintro ⟨_, h⟩ g
      exact (h g).2
    · intro h
      have h1 := h 1
      rw [aut_map_one_apply] at h1
      exact ⟨X.basicOpen_le s h1, fun g ↦ ⟨X.basicOpen_le s h1, h g⟩⟩

variable [Finite G]

theorem exists_isInvariantSection_basicOpen_eq {U : X.Opens} (hU : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U)
    (s : Γ(X, U)) (hs : ∀ g, X.basicOpen s ≤ (ρ g).hom ⁻¹ᵁ X.basicOpen s) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ X.basicOpen t = X.basicOpen s := by
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hU s
  refine ⟨t, ht, le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)⟩
  · have := (hmem x).1 hx 1
    rwa [aut_map_one_apply] at this
  · exact (hmem x).2 fun g ↦ hs g hx

theorem exists_isInvariantSection_basicOpen_le {U : X.Opens} (hU : IsAffineOpen U)
    (hst : ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U) {x : X} (hx : x ∈ U) (O : X.Opens)
    (hO : ∀ g, (ρ g).hom x ∈ O) :
    ∃ t : Γ(X, U), IsInvariantSection ρ U t ∧ x ∈ X.basicOpen t ∧ X.basicOpen t ≤ O := by
  obtain ⟨f, hsf, hfO⟩ := exists_basicOpen_le_of_finite hU O (Set.finite_range fun g ↦ (ρ g).hom x)
    (by rintro _ ⟨g, rfl⟩; exact hst g hx) (by rintro _ ⟨g, rfl⟩; exact hO g)
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hst f
  refine ⟨t, ht, (hmem x).2 fun g ↦ hsf ⟨g, rfl⟩, fun y hy ↦ hfO ?_⟩
  have := (hmem y).1 hy 1
  rwa [aut_map_one_apply] at this

variable (ρ) in

theorem exists_stable_isAffineOpen [OrbitsInAffineOpens ρ] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (∀ g, V ≤ (ρ g).hom ⁻¹ᵁ V) ∧ x ∈ V := by
  obtain ⟨U, hU, hxU⟩ := OrbitsInAffineOpens.exists_isAffineOpen (ρ := ρ) x
  let W : X.Opens := ⨅ g, (ρ g).hom ⁻¹ᵁ U
  have hmemW : ∀ y, y ∈ W ↔ ∀ g, (ρ g).hom y ∈ U := fun y ↦ by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact Iff.rfl
  have hWU : W ≤ U := fun y hy ↦ by
    have := (hmemW y).1 hy 1
    rwa [aut_map_one_apply] at this
  have hWst : ∀ k, W ≤ (ρ k).hom ⁻¹ᵁ W := fun k y hy ↦ by
    show (ρ k).hom y ∈ W
    rw [hmemW]
    intro g
    rw [← aut_map_mul_apply]
    exact (hmemW y).1 hy _
  have hxW : x ∈ W := (hmemW x).2 hxU
  obtain ⟨f, hsf, hfW⟩ := exists_basicOpen_le_of_finite hU W
    (Set.finite_range fun g ↦ (ρ g).hom x)
    (by rintro _ ⟨g, rfl⟩; exact hxU g) (by rintro _ ⟨g, rfl⟩; exact hWst g hxW)
  have hf' : X.basicOpen (X.presheaf.map (homOfLE hWU).op f) = X.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfW
  obtain ⟨t, ht, hmem⟩ := exists_isInvariantSection_mem_basicOpen_iff hWst
    (X.presheaf.map (homOfLE hWU).op f)
  have htf : X.basicOpen t ≤ X.basicOpen f := fun y hy ↦ by
    have := (hmem y).1 hy 1
    rwa [aut_map_one_apply, hf'] at this
  refine ⟨X.basicOpen t, ?_, fun k y hy ↦ ?_, ?_⟩
  · have hA := (hU.basicOpen f).basicOpen (X.presheaf.map (homOfLE hfW).op t)
    rwa [Scheme.basicOpen_res, inf_eq_right.2 htf] at hA
  · show (ρ k).hom y ∈ X.basicOpen t
    rw [hmem]
    intro g
    rw [← aut_map_mul_apply]
    exact (hmem y).1 hy _
  · rw [hmem]
    intro g
    rw [hf']
    exact hsf ⟨g, rfl⟩

end Orbits

end GlobalTheory
