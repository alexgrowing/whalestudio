import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw.CubeGen

section Tools

variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]

def TrivAt (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) : Prop :=
  Triv (LB.LinComb L (fun k => r ≫ φ k) ε)

theorem TrivAt.comp {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {r : Z ⟶ Y} (H : TrivAt L φ ε r)
    (h : Z' ⟶ Z) : TrivAt L φ ε (h ≫ r) := by
  obtain ⟨t, ht⟩ := H
  have e : (fun k => (h ≫ r) ≫ φ k) = fun k => h ≫ r ≫ φ k := funext fun k => Category.assoc _ _ _
  unfold TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ t ht h⟩

theorem triv_pull_iff (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) :
    Triv ((LB.LinComb L φ ε).pull r) ↔ TrivAt L φ ε r := by
  have mem : ∀ (J : PUnit → K → L.ι) (z : Z), z ∈ ((LB.LinComb L φ ε).pull r).U J ↔
      z ∈ LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) := fun J z =>
    mem_pull.trans ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k,
      fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩
  have g : ∀ (J J' : PUnit → K → L.ι) (z : Z), z ∈ ((LB.LinComb L φ ε).pull r).U J →
      z ∈ ((LB.LinComb L φ ε).pull r).U J' →
      gm (𝟙 Z) z (((LB.LinComb L φ ε).pull r).U J ⊓ ((LB.LinComb L φ ε).pull r).U J')
        (((LB.LinComb L φ ε).pull r).g J J') =
      gm (𝟙 Z) z (LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) ⊓ LB.wchart L (fun k => r ≫ φ k) (J' PUnit.unit))
        ((LB.LinComb L (fun k => r ≫ φ k) ε).g (J PUnit.unit) (J' PUnit.unit)) := fun J J' z h h' => by
    refine (gm_pull_g (LB.LinComb L φ ε) r (𝟙 Z) z J J' h h').trans ?_
    refine (gm_linComb L φ ε (𝟙 Z ≫ r) z _ _ (mem_pull.1 h) (mem_pull.1 h')).trans ?_
    refine Eq.trans ?_ (gm_linComb L (fun k => r ≫ φ k) ε (𝟙 Z) z _ _ ((mem J z).1 h) ((mem J' z).1 h')).symm
    simp only [Category.assoc]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun j => res (fun z hz => (mem (fun _ => j) z).2 hz) (t.s fun _ => j)⟩,
      fun j j' => unit_ext fun z hz => ?_⟩
    have hm : (𝟙 Z : Z ⟶ Z) z ∈ ((LB.LinComb L φ ε).pull r).U (fun _ => j) ⊓
      ((LB.LinComb L φ ε).pull r).U (fun _ => j') := ⟨(mem _ z).2 hz.1, (mem _ z).2 hz.2⟩
    have e := congrArg (gm (𝟙 Z) z _) (ht (fun _ => j) (fun _ => j'))
    have e' := (gm_res _ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (g _ _ z hm.1 hm.2) (gm_res _ z _ hm _))))
    exact ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.1 _)).trans (e'.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.2 _)))).symm)
  · rintro ⟨t, ht⟩
    refine ⟨⟨fun J => res (fun z hz => (mem J z).1 hz) (t.s (J PUnit.unit))⟩,
      fun J J' => unit_ext fun z hz => ?_⟩
    have hm : (𝟙 Z : Z ⟶ Z) z ∈ LB.wchart L (fun k => r ≫ φ k) (J PUnit.unit) ⊓
      LB.wchart L (fun k => r ≫ φ k) (J' PUnit.unit) := ⟨(mem _ z).1 hz.1, (mem _ z).1 hz.2⟩
    have e := congrArg (gm (𝟙 Z) z _) (ht (J PUnit.unit) (J' PUnit.unit))
    have e' := (gm_res _ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (g _ _ z hz.1 hz.2).symm (gm_res _ z _ hm _))))
    exact ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.1 _)).trans (e'.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl ((gm_res _ z _ hz _).trans (gm_res _ z _ hz.2 _)))).symm)

theorem trivAt_of_formal {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (r : Z ⟶ Y)
    (h : ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U), ∏ i, k (r ≫ φ i) ^ ε i = 1) : TrivAt L φ ε r := by
  obtain ⟨t, ht, -⟩ := exists_gen hL (φ' := fun i => r ≫ φ i) (ε' := ε)
    (fun U _ k => (Fintype.prod_empty _).trans (h U k).symm) (LB.oneGen L (Y := Z))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact ⟨t, ht⟩

theorem triv_of_local {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ T) (e : T ⟶ Y)
    (he : e ≫ p = 𝟙 T)
    (hF : ∀ (Z : Scheme.{0}) (b : Z ⟶ T) (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
      ∏ i, k ((b ≫ e) ≫ φ i) ^ ε i = 1)
    (hs : ∀ V : T.Opens, ∃ (Z : Scheme.{0}) (m : Z ⟶ Y) (q : Z ⟶ V.toScheme), IsPullback m q p V.ι ∧
      Function.Surjective q.appTop.hom)
    (h : ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ TrivAt L φ ε (p ⁻¹ᵁ U).ι) : Triv (LB.LinComb L φ ε) := by
  have loc : ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε),
      t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ T) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = ((p ⁻¹ᵁ U).ι ≫ p) ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι (((p ⁻¹ᵁ U).ι ≫ p) ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have p' := hF _ ((p ⁻¹ᵁ U).ι ≫ p) V k
        rw [← n₁] at p'
        simp only [Category.assoc] at p'
        refine (Fintype.prod_sum_type _).trans ?_
        simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, p', inv_one, _root_.mul_one])
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, ← Category.assoc, hr,
        Category.assoc b, he, Category.comp_id]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    obtain ⟨W, pr, q, hq, sq⟩ := hs (U s ⊓ U s')
    have mk : ∀ V : T.Opens, U s ⊓ U s' ≤ V → ∃ m : W ⟶ (p ⁻¹ᵁ V).toScheme, m ≫ (p ⁻¹ᵁ V).ι = pr := fun V hV =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ V).ι pr (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) hq.w
        exact (congrArg (· ∈ V) e').mpr (hV (q y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e₀ : (U s ⊓ U s').toScheme ⟶ W := hq.lift ((U s ⊓ U s').ι ≫ e) (𝟙 _)
      (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
    have he₀ : e₀ ≫ pr = (U s ⊓ U s').ι ≫ e := hq.lift_fst _ _ _
    let v : Z ⟶ (U s ⊓ U s').toScheme := IsOpenImmersion.lift (U s ⊓ U s').ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩)
    let ρ : Z ⟶ W := hq.lift (r ≫ (p ⁻¹ᵁ U s).ι) v (IsOpenImmersion.lift_fac _ _ _).symm
    have hρ : ρ ≫ pr = r ≫ (p ⁻¹ᵁ U s).ι := hq.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      q e₀ (hq.lift_snd _ _ _) sq (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm, he₀]),
          hn s' _ _ (U s ⊓ U s').ι y I hI (by rw [Category.assoc, hm', he₀])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩

end Tools

section Fibres

variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem triv_pull_comp_iff (q : W ⟶ Y) {Z : Scheme.{0}} (π : Z ⟶ W) :
    Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) ↔ TrivAt L φ ε (π ≫ q) := by
  rw [triv_pull_iff]
  unfold TrivAt
  simp only [Category.assoc]

def fibTriv (p : Y ⟶ T) : Set T :=
  {t | ∃ (F : Type) (_ : Field F) (g : Spec (CommRingCat.of F) ⟶ T) (Z : Scheme.{0}) (π : Z ⟶ Y)
    (f' : Z ⟶ Spec (CommRingCat.of F)), t ∈ Set.range g ∧ IsPullback π f' p g ∧ TrivAt L φ ε π}

def locTriv (p : Y ⟶ T) : Set T := {t | ∃ U : T.Opens, t ∈ U ∧ TrivAt L φ ε (p ⁻¹ᵁ U).ι}

theorem isOpen_locTriv (p : Y ⟶ T) : IsOpen (locTriv L φ ε p) :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, hU, h⟩ => ⟨U, fun _ hy => ⟨U, hy, h⟩, U.isOpen, hU⟩

theorem locTriv_subset (p : Y ⟶ T) : locTriv L φ ε p ⊆ fibTriv L φ ε p := by
  rintro t ⟨U, hU, h⟩
  have hr : Set.range (T.fromSpecResidueField t) = {t} := Scheme.range_fromSpecResidueField t
  refine ⟨T.residueField t, inferInstance, T.fromSpecResidueField t, _, _, _, hr.ge rfl,
    IsPullback.of_hasPullback p (T.fromSpecResidueField t), ?_⟩
  have := h.comp (IsOpenImmersion.lift (p ⁻¹ᵁ U).ι (pullback.fst p (T.fromSpecResidueField t)) (by
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    intro y hy
    exact (congrArg (· ∈ U) hy).mpr hU))
  rwa [IsOpenImmersion.lift_fac] at this

theorem mem_range_spec {R F : Type} [CommRing R] [Field F] (g : R →+* F) (x : PrimeSpectrum R) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom g)) ↔ RingHom.ker g = x.asIdeal := by
  have key : ∀ y : PrimeSpectrum F, (PrimeSpectrum.comap g y).asIdeal = RingHom.ker g := fun y => by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime y.asIdeal]; rfl
  constructor
  · rintro ⟨y, rfl⟩
    exact (key y).symm
  · intro h
    exact ⟨(default : PrimeSpectrum F), PrimeSpectrum.ext ((key _).trans h)⟩

theorem mem_fibTriv_iff {p : Y ⟶ T} {R : Type} [CommRing R] {j : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion j]
    {q : W ⟶ Y} {f : W ⟶ Spec (CommRingCat.of R)} (H : IsPullback q f p j) (x : PrimeSpectrum R) :
    j x ∈ fibTriv L φ ε p ↔ ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
      (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
      Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) := by
  constructor
  · rintro ⟨F, _, g, Z, π, f', ⟨y, hy⟩, hp, ht⟩
    have hsub : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    obtain ⟨g', hg'⟩ : ∃ g' : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R), g' ≫ j = g :=
      ⟨IsOpenImmersion.lift j g (by
        rintro _ ⟨y', rfl⟩
        rw [Subsingleton.elim y' y, hy]
        exact ⟨x, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨g₀, rfl⟩ := Spec.map_surjective g'
    subst hg'
    have w : π ≫ p = (f' ≫ Spec.map g₀) ≫ j := by rw [hp.w, Category.assoc]
    have e : H.lift π _ w ≫ q = π := H.lift_fst _ _ _
    refine ⟨F, inferInstance, g₀.hom, Z, H.lift π _ w, f', ?_, ?_, ?_⟩
    · exact (mem_range_spec g₀.hom x).1 ⟨y, j.isOpenEmbedding.injective hy⟩
    · exact IsPullback.of_right (by rw [e]; exact hp) (H.lift_snd _ _ _) H
    · rw [triv_pull_comp_iff, e]; exact ht
  · rintro ⟨F, _, g, Z, π, f', hk, hp, ht⟩
    obtain ⟨y, hy⟩ := (mem_range_spec g x).2 hk
    exact ⟨F, inferInstance, Spec.map (CommRingCat.ofHom g) ≫ j, Z, π ≫ q, f', ⟨y, congrArg j hy⟩,
      hp.paste_horiz H, (triv_pull_comp_iff L φ ε q π).1 ht⟩

theorem fibTriv_clopen (p : Y ⟶ T)
    (h : ∀ (R : Type) [CommRing R] (j : Spec (CommRingCat.of R) ⟶ T), ∃ (W : Scheme.{0}) (q : W ⟶ Y)
      (f : W ⟶ Spec (CommRingCat.of R)), IsPullback q f p j ∧
      IsClosed {x : PrimeSpectrum R | ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
        (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
        Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π)} ∧
      ∀ (F : Type) [Field F] (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W) (f' : Z ⟶ Spec (CommRingCat.of F)),
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) →
        ∃ r : R, g r ≠ 0 ∧
          Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull (f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι)) :
    fibTriv L φ ε p ⊆ locTriv L φ ε p ∧ IsClosed (fibTriv L φ ε p) := by
  have chart : ∀ t : T, ∃ (R : Type) (_ : CommRing R) (j : Spec (CommRingCat.of R) ⟶ T) (_ : IsOpenImmersion j)
      (x : PrimeSpectrum R), j x = t := fun t => by
    obtain ⟨_, ⟨U, hU, rfl⟩, ht, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
    obtain ⟨x, hx⟩ := hU.range_fromSpec.ge ht
    exact ⟨Γ(T, U), inferInstance, hU.fromSpec, hU.isOpenImmersion_fromSpec, x, hx⟩
  constructor
  · intro t ht
    obtain ⟨R, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, -, ho⟩ := h R j
    obtain ⟨F, _, g, Z, π, f', hk, hp, ht⟩ := (mem_fibTriv_iff L φ ε H x).1 ht
    obtain ⟨r, hr, hT⟩ := ho F g Z π f' hp ht
    rw [triv_pull_comp_iff] at hT
    have : IsOpenImmersion q := MorphismProperty.of_isPullback H.flip ‹_›
    refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen r), ⟨x, ?_, rfl⟩, ?_⟩
    · show r ∉ x.asIdeal
      rw [← hk]; exact hr
    · have := hT.comp (IsOpenImmersion.lift ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι ≫ q)
        (p ⁻¹ᵁ (j ''ᵁ (PrimeSpectrum.basicOpen r))).ι (by
          rintro _ ⟨y, rfl⟩
          obtain ⟨x', hx', e⟩ := y.2
          obtain ⟨w, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback H y.1 x' e.symm
          exact ⟨⟨w, (congrArg (· ∈ PrimeSpectrum.basicOpen r) h₂).mpr hx'⟩, h₁⟩))
      exact (congrArg (TrivAt L φ ε) (IsOpenImmersion.lift_fac _ _ _)).mp this
  · refine ⟨isOpen_iff_forall_mem_open.2 fun t ht => ?_⟩
    obtain ⟨R, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, hc, -⟩ := h R j
    refine ⟨j '' _, ?_, j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl, x,
      fun hx => ht ((mem_fibTriv_iff L φ ε H x).2 hx), rfl⟩
    rintro _ ⟨y, hy, rfl⟩ hy'
    exact hy ((mem_fibTriv_iff L φ ε H y).1 hy')

end Fibres

section Cube

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

omit [GrpObj A] in

theorem exists_cube_chart {T : Scheme.{0}} (j : T ⟶ A.left) :
    ∃ q : ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).left ⟶ (G3 A).left,
      IsPullback q ((Over.pullback (j ≫ A.hom)).obj A ⊗ (Over.pullback (j ≫ A.hom)).obj A).hom (x3 A 2).left j ∧
      q ≫ (x3 A 0).left = (fst _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (x3 A 1).left = (snd _ _ : _ ⟶ (Over.pullback (j ≫ A.hom)).obj A).left ≫ pullback.fst A.hom (j ≫ A.hom) := by
  set B := (Over.pullback (j ≫ A.hom)).obj A
  have hB : IsPullback (pullback.fst A.hom (j ≫ A.hom)) B.hom A.hom (j ≫ A.hom) := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have h3 : IsPullback (fst A (A ⊗ A)).left (snd A (A ⊗ A)).left A.hom (A ⊗ A).hom := IsPullback.of_hasPullback _ _
  have hBB : IsPullback (fst B B).left (snd B B).left B.hom B.hom := IsPullback.of_hasPullback _ _
  obtain ⟨m, m₁, m₂⟩ : ∃ m : B.left ⟶ (A ⊗ A).left, m ≫ (fst A A).left = pullback.fst A.hom (j ≫ A.hom) ∧
      m ≫ (snd A A).left = B.hom ≫ j :=
    ⟨h2.lift _ _ (by rw [hB.w, Category.assoc]), h2.lift_fst _ _ _, h2.lift_snd _ _ _⟩
  have hm : IsPullback m B.hom (snd A A).left j := IsPullback.of_right (by rw [m₁]; exact hB) m₂ h2
  have mw : m ≫ (A ⊗ A).hom = B.hom ≫ j ≫ A.hom := by
    rw [← Over.w (snd A A), ← Category.assoc, m₂, Category.assoc]
  have ho : IsPullback ((fst B B).left ≫ pullback.fst A.hom (j ≫ A.hom)) (snd B B).left A.hom (m ≫ (A ⊗ A).hom) := by
    rw [mw]; exact hBB.paste_horiz hB
  obtain ⟨q, q₁, q₂⟩ : ∃ q : (B ⊗ B).left ⟶ (G3 A).left,
      q ≫ (fst A (A ⊗ A)).left = (fst B B).left ≫ pullback.fst A.hom (j ≫ A.hom) ∧
      q ≫ (snd A (A ⊗ A)).left = (snd B B).left ≫ m :=
    ⟨h3.lift _ _ (by rw [ho.w, Category.assoc]), h3.lift_fst _ _ _, h3.lift_snd _ _ _⟩
  have hq : IsPullback q (snd B B).left (snd A (A ⊗ A)).left m := IsPullback.of_right (by rw [q₁]; exact ho) q₂ h3
  refine ⟨q, ?_, q₁, ?_⟩
  · rw [← Over.w (snd B B)]
    exact hq.paste_vert hm
  · show q ≫ (snd A (A ⊗ A)).left ≫ (fst A A).left = _
    rw [← Category.assoc, q₂, Category.assoc, m₁]

variable {A}

theorem prod_face [IsCommMonObj A] {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (x3 A i).left = b ≫ η[A].left) (U : Type) [CommGroup U] (k : (Z ⟶ A.left) → U) :
    ∏ I, k (r ≫ thφ A (x3 A) I) ^ thε I = 1 := by
  let T : Over S := Over.mk (r ≫ (G3 A).hom)
  let x : T ⟶ G3 A := Over.homMk r rfl
  have hb : b = r ≫ (G3 A).hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  have hi : x ≫ x3 A i = 1 := by
    apply Over.OverMorphism.ext
    rw [Hom.one_def]
    exact h.trans (by rw [hb]; rfl)
  have hx : lift (x ≫ x3 A 0) (lift (x ≫ x3 A 1) (x ≫ x3 A 2)) = x := by ext <;> simp [x3]
  have := prod_cub (x ≫ x3 A 0) (x ≫ x3 A 1) (x ≫ x3 A 2) (U := U) k
  rw [hx] at this
  refine this.trans ?_
  fin_cases i
  · rw [show x ≫ x3 A 0 = 1 from hi]
    simp only [_root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · rw [show x ≫ x3 A 1 = 1 from hi]
    simp only [_root_.one_mul, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · rw [show x ≫ x3 A 2 = 1 from hi]
    simp only [_root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

theorem one_left_fst {S' : Scheme.{0}} (f : S' ⟶ S) (T : Over S') :
    (1 : T ⟶ (Over.pullback f).obj A).left ≫ pullback.fst A.hom f = (T.hom ≫ f) ≫ η[A].left :=
  congrArg (fun z => z.left) (map_one (pushHom (isGrpPullback_pullback A f) T))

theorem isAb_baseChange (hA : IsAbelianScheme A) {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

end Cube

end GlobalTheory.AbLaw.CubeGen

namespace GlobalTheory.AbLaw

open CubeGen

theorem exists_gen_theta :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → GlobalFnsSt → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → IsProjBy f → ∀ M : LB X, M.IsLB → Nonempty (Perf f M)) → (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))), IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}) → (∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A], IsAbelianScheme A → ∀ M : LB (A ⊗ A).left, M.IsLB → Nonempty (Perf (A ⊗ A).hom M) → Triv (M.pull (lift (𝟙 A) 1).left) → Triv (M.pull (lift 1 (𝟙 A)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (A ⊗ A).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (A ⊗ A).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((A ⊗ A).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι)) → ∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen := by
  intro hI hG hPerf hProj hSegre hClosed hOpen S P M hM
  have hA := P.isAb
  have := hA.comm
  have := hA.geomConnected
  have H := fibTriv_clopen M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart P.A j
    have hB := isAb_baseChange hA (j ≫ P.A.hom)
    have one := one_left_fst (A := P.A) (j ≫ P.A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ P.A.hom)).obj P.A).hom := by
      obtain ⟨N, -, m, s, h₁, h₂⟩ := hProj S P R (j ≫ P.A.hom) _ _ _ (IsPullback.of_hasPullback _ _)
      exact ⟨_, h₁, m, s, h₂⟩
    let B := (Over.pullback (j ≫ P.A.hom)).obj P.A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ thφ P.A (x3 P.A) k) thε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := hPerf R _ _ sm (hSegre R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, hClosed R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr (hI _ _ _ sm gc),
      fun F _ g Z π f' => hOpen R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 1 (B.hom ≫ j ≫ P.A.hom) ?_)
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine trivAt_of_formal hM _ (prod_face _ 0 (B.hom ≫ j ≫ P.A.hom) ?_)
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M (thφ P.A (x3 P.A)) thε (x3 P.A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (P.A.hom t)) = {P.A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (P.A.hom t) ≫ η[P.A].left
    have gw : g ≫ P.A.hom = S.fromSpecResidueField (P.A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (P.A.hom.isConnected_preimage_singleton (P.A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (P.A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (P.A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 P.A 2).left g,
      trivAt_of_formal hM _ (prod_face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (P.A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm))⟩
  let e : P.A ⟶ G3 P.A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 P.A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 P.A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM (thφ P.A (x3 P.A)) thε (x3 P.A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => prod_face _ 0 (b ≫ P.A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart P.A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ P.A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

end GlobalTheory.AbLaw
