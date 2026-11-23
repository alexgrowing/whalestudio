import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SegreCoord

variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']

def ev (y : Sp T) : T →+* (Sp T).presheaf.stalk y :=
  ((Sp T).presheaf.germ ⊤ y trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom

theorem ev_eq (y : Sp T) (t : T) : ev y t = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom t) := by
  rw [gs_eq (𝟙 _) y ⊤ trivial]; rfl

theorem ev_ext {a b : T} (h : ∀ y : Sp T, ev y a = ev y b) : a = b :=
  (Scheme.ΓSpecIso (CommRingCat.of T)).symm.commRingCatIsoToRingEquiv.injective
    (fn_ext (V := ⊤) fun y _ => (ev_eq y a).symm.trans ((h y).trans (ev_eq y b)))

theorem isUnit_of_ev {a : T} (h : ∀ y : Sp T, IsUnit (ev y a)) : IsUnit a := by
  have := (Sp T).toRingedSpace.isUnit_of_isUnit_germ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a)
    fun y _ => h y
  simpa using this.map (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom

theorem gs_stalkMap {Y Y' : Scheme.{0}} (r : Y' ⟶ Y) (x : Y ⟶ X) (z : Y') (U : X.Opens) (h : x (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ x) z U a = (r.stalkMap z).hom (gs x (r z) U a) := by
  rw [gs_eq (r ≫ x) z U h, gs_eq x (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (x ⁻¹ᵁ U) z h _).symm

theorem ev_stalkMap (φ : T →+* T') (z : Sp T') (t : T) :
    ev z (φ t) = ((spMap φ).stalkMap z).hom (ev (spMap φ z) t) := by
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply (spMap φ) ⊤ z trivial _).symm
  have := congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg ((Sp T').presheaf.germ ⊤ z trivial).hom this

theorem gs_appLE {Y : Scheme.{0}} (x : Y ⟶ X) (y : Y) {U : X.Opens} {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((x.appLE U V h).hom a) = gs x y U a :=
  (gs_res (𝟙 Y) y h hy _).trans ((gs_pull (𝟙 Y) x y U (h hy) a).trans (by rw [Category.id_comp]))

theorem gs_sec (s : M.Sec) {Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) {j j' : M.ι} (h : r z ∈ M.U j) (h' : r z ∈ M.U j') :
    gs r z _ (s.f j) = (gm r z _ (M.g j j')).val * gs r z _ (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨h, h'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

variable (M th) in

def Loc (x : Sp T ⟶ X) (v : σ → T) : Prop :=
  ∀ (y : Sp T) (j : M.ι), x y ∈ M.U j → ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((th i).f j) = ev y (v i) * u

theorem loc_of_secCoord {x : Sp T ⟶ X} {v : σ → T} (h : SecCoord M th x v) : Loc M th x v := by
  obtain ⟨τ, -, h⟩ := h
  intro y j hy
  have hy' : y ∈ (M.pull x).U (fun _ => j) := mem_pull.2 hy
  refine ⟨gm (𝟙 _) y _ (τ.s fun _ => j), fun i => ?_⟩
  have := congrArg (gs (𝟙 _) y _) (h i (fun _ => j) (fun z hz => mem_pull.1 hz))
  refine (gs_appLE x y _ hy' _).symm.trans (this.trans ((gs_mul _ y _ hy' _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (gs_res _ y _ hy' _).trans (ev_eq y _).symm
  · exact gs_unit _ y _ hy' _

theorem secCoord_mk {x : Sp T ⟶ X} {v : σ → T} (t : ∀ j : PUnit → M.ι, Γ(Sp T, (M.pull x).U j))
    (c : ∀ (y : Sp T), M.ι → (Sp T).presheaf.stalk y)
    (ht : ∀ j y, y ∈ (M.pull x).U j → gs (𝟙 _) y _ (t j) = c y (j PUnit.unit))
    (hu : ∀ y j, x y ∈ M.U j → IsUnit (c y j))
    (hc : ∀ y j j', x y ∈ M.U j → x y ∈ M.U j' → c y j = (gm x y _ (M.g j j')).val * c y j')
    (hv : ∀ y j i, x y ∈ M.U j → gs x y _ ((th i).f j) = ev y (v i) * c y j) : SecCoord M th x v := by
  have hU : ∀ j, IsUnit (t j) := fun j => (Sp T).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
    (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (ht j y hy))).mpr (hu y _ (mem_pull.1 hy))
  refine ⟨⟨fun j => (hU j).unit⟩, fun j j' => Units.ext (fn_ext fun y hy => ?_), fun i j h => fn_ext fun y hy => ?_⟩
  · refine ((gs_res (𝟙 _) y inf_le_left hy (t j)).trans (ht j y hy.1)).trans (Eq.trans ?_
      ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 _) y _ hy _).trans
        (congrArg Units.val (gm_pull_g M x (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 _) y inf_le_right hy (t j')).trans (ht j' y hy.2)))).symm)
    rw [Category.id_comp]
    exact hc y _ _ (mem_pull.1 hy.1) (mem_pull.1 hy.2)
  · refine (gs_appLE x y _ hy _).trans ((hv y _ i (mem_pull.1 hy)).trans (Eq.symm ?_))
    exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans (ev_eq y _).symm) (ht j y hy))

theorem gs_sum {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (s : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  simp only [gs_eq f y U h, map_sum]

theorem exists_comb {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤) :
    ∃ (s : Finset σ) (c : σ → T), ∑ i ∈ s, c i * v i = 1 := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (show (1 : T) ∈ Submodule.span T (Set.range v) from (Ideal.eq_top_iff_one _).1 hv)
  exact ⟨c.support, c, hc⟩

theorem secCoord_of_loc {x : Sp T ⟶ X} {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤) (h : Loc M th x v) :
    SecCoord M th x v := by
  obtain ⟨s, c, hc⟩ := exists_comb hv
  have key : ∀ y j, x y ∈ M.U j → ∀ u : ((Sp T).presheaf.stalk y)ˣ, (∀ i, gs x y _ ((th i).f j) = ev y (v i) * u) →
      ∑ i ∈ s, ev y (c i) * gs x y _ ((th i).f j) = u := fun y j _ u hu => by
    simp only [hu, ← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hc, map_one, one_mul]
  refine secCoord_mk (fun j => ∑ i ∈ s, resG (Sp T) le_top ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (c i)) *
    (x.appLE _ _ (fun z hz => mem_pull.1 hz)).hom ((th i).f (j PUnit.unit)))
    (fun y j => ∑ i ∈ s, ev y (c i) * gs x y _ ((th i).f j)) (fun j y hy => ?_) (fun y j hy => ?_)
    (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)
  · refine (gs_sum _ y _ hy _ _).trans (Finset.sum_congr rfl fun i _ => (gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans (ev_eq y _).symm) (gs_appLE x y _ hy _)
  · obtain ⟨u, hu⟩ := h y j hy
    rw [key y j hy u hu]; exact u.isUnit
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [gs_sec (th i) x y hy hy', mul_left_comm]
  · obtain ⟨u, hu⟩ := h y j hy
    rw [key y j hy u hu, hu]

theorem exists_secCoord (hM : M.IsLB) {x : Sp T ⟶ X} {k : M.ι} (hk : ∀ y, x y ∈ M.U k) : ∃ v, SecCoord M th x v := by
  have le : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U k) := fun j y hy => ⟨mem_pull.1 hy, hk y⟩
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom ((x.appLE (M.U k) ⊤ (fun y _ => hk y)).hom ((th i).f k)),
    secCoord_mk (fun j => (x.appLE _ _ (le j)).hom (M.g (j PUnit.unit) k).val)
    (fun y j => gs x y _ (M.g j k).val) (fun j y hy => gs_appLE x y _ hy _) (fun y j hy => ?_)
    (fun y j j' hy hy' => ?_) (fun y j i hy => ?_)⟩
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩]; exact Units.isUnit _
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩, gs_unit x y (M.U _ ⊓ M.U k) ⟨hy', hk y⟩, ← Units.val_mul, gm_cocycle hM x y hy hy' (hk y)]
  · rw [gs_unit x y (M.U _ ⊓ M.U k) ⟨hy, hk y⟩, gs_sec (th i) x y hy (hk y), mul_comm, ev_eq]
    congr 1
    rw [← gs_appLE x y (V := ⊤) (fun y _ => hk y) trivial]
    congr 1
    simp

theorem Loc.baseChange {x : Sp T ⟶ X} {v : σ → T} (h : Loc M th x v) (φ : T →+* T') :
    Loc M th (spMap φ ≫ x) (fun i => φ (v i)) := fun z j hz => by
  obtain ⟨u, hu⟩ := h (spMap φ z) j hz
  refine ⟨Units.map ((spMap φ).stalkMap z).hom.toMonoidHom u, fun i => ?_⟩
  rw [gs_stalkMap _ x z _ hz, hu, map_mul, ev_stalkMap]; rfl

theorem Loc.smul {x : Sp T ⟶ X} {v : σ → T} (h : Loc M th x v) {t : T} (ht : IsUnit t) :
    Loc M th x (fun i => t * v i) := fun z j hz => by
  obtain ⟨u, hu⟩ := h z j hz
  obtain ⟨t, rfl⟩ := ht
  refine ⟨Units.map (ev z).toMonoidHom t⁻¹ * u, fun i => ?_⟩
  have : ev z t.val * ev z (t⁻¹).val = 1 := by rw [← map_mul, t.mul_inv, map_one]
  rw [hu, map_mul]
  show _ = _ * _ * (ev z (t⁻¹).val * u.val)
  linear_combination (-(ev z (v i) * u.val)) * this

theorem Loc.unique (hM : M.IsLB) {x : Sp T ⟶ X} {v w : σ → T} (h : Loc M th x v) (h' : Loc M th x w)
    (hv : Ideal.span (Set.range v) = ⊤) : ∃ t : T, IsUnit t ∧ ∀ i, w i = t * v i := by
  obtain ⟨s, c, hc⟩ := exists_comb hv
  have key : ∀ y : Sp T, ∃ u : ((Sp T).presheaf.stalk y)ˣ, (∀ i, ev y (w i) = u * ev y (v i)) ∧
      ev y (∑ i ∈ s, c i * w i) = u := fun y => by
    obtain ⟨j, hj⟩ := exists_chart hM (x y)
    obtain ⟨u, hu⟩ := h y j hj
    obtain ⟨u', hu'⟩ := h' y j hj
    have e : ∀ i, ev y (w i) = (u * u'⁻¹ :).val * ev y (v i) := fun i => by
      rw [Units.val_mul, mul_comm, ← mul_assoc, ← hu, hu', Units.mul_inv_cancel_right]
    refine ⟨u * u'⁻¹, e, ?_⟩
    simp only [map_sum, map_mul, e, mul_left_comm _ (u * u'⁻¹ :).val]
    simp only [← map_mul, ← Finset.mul_sum, ← map_sum, hc, map_one, mul_one]
  refine ⟨∑ i ∈ s, c i * w i, isUnit_of_ev fun y => ?_, fun i => ev_ext fun y => ?_⟩
  · obtain ⟨u, -, e⟩ := key y
    rw [e]; exact u.isUnit
  · obtain ⟨u, e', e⟩ := key y
    rw [map_mul, e, e']

theorem loc_of_away {x : Sp T ⟶ X} {v : σ → T}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal, Loc M th (spMap (algebraMap T (Localization.Away f)) ≫ x)
      (fun i => algebraMap T (Localization.Away f) (v i))) : Loc M th x v := fun y j hy => by
  obtain ⟨f, hf, h⟩ := h y
  obtain ⟨z, rfl⟩ : ∃ z, spMap (algebraMap T (Localization.Away f)) z = y := by
    have : (y : PrimeSpectrum T) ∈ Set.range (PrimeSpectrum.comap (algebraMap T (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ f]; exact hf
    exact this
  obtain ⟨u, hu⟩ := h z j hy
  let e := (asIso ((spMap (algebraMap T (Localization.Away f))).stalkMap z)).commRingCatIsoToRingEquiv
  refine ⟨Units.map e.symm.toMonoidHom u, fun i => e.injective ?_⟩
  have := hu i
  rw [gs_stalkMap _ x z _ hy, ev_stalkMap] at this
  rw [map_mul]
  exact this.trans (congrArg _ (e.apply_symm_apply _).symm)

theorem exists_away (W : (Sp T).Opens) (y : Sp T) (hy : y ∈ W) :
    ∃ f ∉ (show PrimeSpectrum T from y).asIdeal, ∀ z, spMap (algebraMap T (Localization.Away f)) z ∈ W := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hy W.2
  refine ⟨f, hf, fun z => hle ?_⟩
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le ⟨z, rfl⟩

theorem eq_top_of_away {J : Ideal T}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal, J.map (algebraMap T (Localization.Away f)) = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := J.exists_le_maximal hJ
  obtain ⟨f, hf, e⟩ := h ⟨m, hm.isPrime⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) _).1
    ((Ideal.eq_top_iff_one _).1 e)
  rw [one_mul] at ha
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) _).1 ha
  have : f ^ k * f ^ n ∈ m := by
    have e : f ^ k * f ^ n = f ^ k * a := hk
    rw [e]; exact m.mul_mem_left _ (hle a.2)
  rw [← pow_add] at this
  exact hf (hm.isPrime.mem_of_pow_mem _ this)

theorem eq_of_away {a b : T}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal,
      algebraMap T (Localization.Away f) a = algebraMap T (Localization.Away f) b) : a = b := by
  refine ev_ext fun y => ?_
  obtain ⟨f, hf, h⟩ := h y
  obtain ⟨z, rfl⟩ : ∃ z, spMap (algebraMap T (Localization.Away f)) z = y := by
    have : (y : PrimeSpectrum T) ∈ Set.range (PrimeSpectrum.comap (algebraMap T (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ f]; exact hf
    exact this
  let e := (asIso ((spMap (algebraMap T (Localization.Away f))).stalkMap z)).commRingCatIsoToRingEquiv
  exact e.injective ((ev_stalkMap _ z a).symm.trans ((congrArg (ev z) h).trans (ev_stalkMap _ z b)))

theorem hom_ext_away {x x' : Sp T ⟶ X}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal, spMap (algebraMap T (Localization.Away f)) ≫ x =
      spMap (algebraMap T (Localization.Away f)) ≫ x') : x = x' := by
  choose f hf h using h
  have hs : Ideal.span (Set.range f) = ⊤ := by
    by_contra hJ
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
    exact hf ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  exact (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of T) f hs).openCover.hom_ext _ _ h

theorem span_map {v : σ → T} (φ : T →+* T') :
    Ideal.span (Set.range fun i => φ (v i)) = (Ideal.span (Set.range v)).map φ := by
  rw [Ideal.map_span, ← Set.range_comp]; rfl

theorem unimod_map {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤) (φ : T →+* T') :
    Ideal.span (Set.range fun i => φ (v i)) = ⊤ := by rw [span_map, hv, Ideal.map_top]

theorem unimod_smul {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤) {t : T} (ht : IsUnit t) :
    Ideal.span (Set.range fun i => t * v i) = ⊤ := by
  obtain ⟨t, rfl⟩ := ht
  rw [eq_top_iff, ← hv, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← t.inv_mul_cancel_left (v i)]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem unimod_mul {v₁ v₂ : σ → T} (h₁ : Ideal.span (Set.range v₁) = ⊤) (h₂ : Ideal.span (Set.range v₂) = ⊤) :
    Ideal.span (Set.range fun i : σ × σ => v₁ i.1 * v₂ i.2) = ⊤ := by
  rw [eq_top_iff, ← Ideal.top_mul ⊤]
  nth_rewrite 1 [← h₁, ← h₂]
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  exact Ideal.subset_span ⟨(i, j), rfl⟩

theorem exists_unit_of_mul_eq {v₁ v₂ w₁ w₂ : σ → T} {t : T} (h₁ : Ideal.span (Set.range w₁) = ⊤)
    (h₂ : Ideal.span (Set.range w₂) = ⊤) (e : ∀ i j, w₁ i * w₂ j = t * (v₁ i * v₂ j)) :
    ∃ u, IsUnit u ∧ ∀ i, w₁ i = u * v₁ i := by
  obtain ⟨s, c, hc⟩ := exists_comb h₂
  obtain ⟨s', c', hc'⟩ := exists_comb h₁
  have : ∀ i, w₁ i = (t * ∑ j ∈ s, c j * v₂ j) * v₁ i := fun i => by
    rw [← mul_one (w₁ i), ← hc, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by linear_combination c j * e i j
  refine ⟨_, IsUnit.of_mul_eq_one (∑ i ∈ s', c' i * v₁ i) ?_, this⟩
  rw [← hc', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [this i]; ring

section Rep
variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} (H : ProjRep I s M th)
include H

theorem rep_chart {β : R →+* T} {x : Sp T ⟶ X} (hx : x ≫ s = spMap β) {k : M.ι} (hk : ∀ y, x y ∈ M.U k) :
    ∃ v, Loc M th x v ∧ Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0 := by
  obtain ⟨v, hv⟩ := exists_secCoord (th := th) H.1 hk
  exact ⟨v, loc_of_secCoord hv, H.2.1 T β x v hx hv⟩

theorem rep_unique {β : R →+* T} {x x' : Sp T ⟶ X} (hx : x ≫ s = spMap β) (hx' : x' ≫ s = spMap β) {v : σ → T}
    (hv : Ideal.span (Set.range v) = ⊤) (h : Loc M th x v) (h' : Loc M th x' v) : x = x' :=
  (H.2.2 T β v hv (H.2.1 T β x v hx (secCoord_of_loc hv h)).2).unique ⟨hx, secCoord_of_loc hv h⟩
    ⟨hx', secCoord_of_loc hv h'⟩

theorem rep_smul {β : R →+* T} {v : σ → T} (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) (t : T) :
    ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => t * v i) F = 0 := by
  intro F hF
  let L := Localization.Away (Polynomial.X : Polynomial T)
  let φ : T →+* L := (algebraMap (Polynomial T) L).comp Polynomial.C
  have hu : IsUnit (algebraMap (Polynomial T) L Polynomial.X) := IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨x, ⟨hx, hc⟩, -⟩ := H.2.2 L (φ.comp β) (fun i => φ (v i)) (unimod_map hv φ) fun G hG => by
    have := MvPolynomial.eval₂_comp_left φ β v G
    rw [h G hG, map_zero] at this
    exact this.symm
  have h1 := (H.2.1 L _ x _ hx (secCoord_of_loc (unimod_smul (unimod_map hv φ) hu)
    ((loc_of_secCoord hc).smul hu))).2 F hF
  have h2 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply IsLocalization.injective L (M := Submonoid.powers (Polynomial.X : Polynomial T))
      (Submonoid.powers_le.2 Polynomial.X_mem_nonzeroDivisors)
    rw [MvPolynomial.eval₂_comp_left, map_zero, ← h1]
    congr 1
    funext i
    exact map_mul _ _ _
  have h3 := congrArg (Polynomial.evalRingHom t) h2
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h3
  rw [← h3]
  congr 1
  · ext; simp
  · funext i; simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]

end Rep

section Box
variable {Y : Scheme.{0}} (p q : Y ⟶ X)

theorem gs_appLE' {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {U : X.Opens} {V : Y.Opens} (h : V ≤ p ⁻¹ᵁ U) (hz : r z ∈ V)
    (a : Γ(X, U)) : gs r z V ((p.appLE U V h).hom a) = gs (r ≫ p) z U a :=
  (gs_res r z h hz _).trans (gs_pull r p z U (h hz) a)

variable (M) in

abbrev boxLB : LB Y := LB.LinComb M (K := Fin 2) ![p, q] (fun _ => 1)

def boxF (a b : M.Sec) (j : Fin 2 → M.ι) : Γ(Y, LB.wchart M ![p, q] j) :=
  (p.appLE _ _ (LB.wchart_le M ![p, q] j 0)).hom (a.f (j 0)) * (q.appLE _ _ (LB.wchart_le M ![p, q] j 1)).hom (b.f (j 1))

theorem gs_boxF (a b : M.Sec) (j : Fin 2 → M.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart M ![p, q] j) :
    gs r z _ (boxF p q a b j) = gs (r ≫ p) z _ (a.f (j 0)) * gs (r ≫ q) z _ (b.f (j 1)) :=
  (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_appLE' p r z _ hz _) (gs_appLE' q r z _ hz _))

def boxSec (a b : M.Sec) : (boxLB M p q).Sec where
  f := boxF p q a b
  compat j j' := fn_ext fun y hy => by
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_boxF p q a b j _ y hy.1)).trans (Eq.trans ?_
      ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 Y) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (gs_boxF p q a b j' _ y hy.2)))).symm)
    rw [gs_sec a (𝟙 Y ≫ p) y (LB.wchart_le M ![p, q] j 0 hy.1) (LB.wchart_le M ![p, q] j' 0 hy.2),
      gs_sec b (𝟙 Y ≫ q) y (LB.wchart_le M ![p, q] j 1 hy.1) (LB.wchart_le M ![p, q] j' 1 hy.2),
      Fin.prod_univ_two, zpow_one, zpow_one, Units.val_mul, mul_mul_mul_comm]
    rfl

variable (th) in

def boxTh (i : σ × σ) : (boxLB M p q).Sec := boxSec p q (th i.1) (th i.2)

theorem loc_box {x : Sp T ⟶ Y} {v₁ v₂ : σ → T} (h₁ : Loc M th (x ≫ p) v₁) (h₂ : Loc M th (x ≫ q) v₂) :
    Loc (boxLB M p q) (boxTh th p q) x (fun i => v₁ i.1 * v₂ i.2) := fun y j hy => by
  obtain ⟨u₁, e₁⟩ := h₁ y (j 0) (LB.wchart_le M ![p, q] j 0 hy)
  obtain ⟨u₂, e₂⟩ := h₂ y (j 1) (LB.wchart_le M ![p, q] j 1 hy)
  refine ⟨u₁ * u₂, fun i => (gs_boxF p q _ _ j x y hy).trans ?_⟩
  rw [e₁, e₂, map_mul, Units.val_mul, mul_mul_mul_comm]

end Box

section Segre
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))

open MvPolynomial in

def segreIdeal : Ideal (MvPolynomial (σ × σ) R) :=
  Ideal.span ({G | ∃ a b c d, G = MvPolynomial.X (a, b) * MvPolynomial.X (c, d) -
      MvPolynomial.X (a, d) * MvPolynomial.X (c, b)} ∪
    {G | ∃ b, ∃ F ∈ I, G = rename (fun i => (i, b)) F} ∪ {G | ∃ a, ∃ F ∈ I, G = rename (fun i => (a, i)) F})

def RankOne (β : R →+* T) (w : σ × σ → T) : Prop :=
  (∀ a b c d, w (a, b) * w (c, d) = w (a, d) * w (c, b)) ∧
    (∀ b, ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => w (i, b)) F = 0) ∧
    (∀ a, ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => w (a, i)) F = 0)

theorem killed_iff (β : R →+* T) (w : σ × σ → T) :
    (∀ G ∈ segreIdeal I, MvPolynomial.eval₂ β w G = 0) ↔ RankOne I β w := by
  constructor
  · intro h
    refine ⟨fun a b c d => ?_, fun b F hF => ?_, fun a F hF => ?_⟩
    · have := h _ (Ideal.subset_span (Or.inl (Or.inl ⟨a, b, c, d, rfl⟩)))
      simpa [sub_eq_zero] using this
    · have := h _ (Ideal.subset_span (Or.inl (Or.inr ⟨b, F, hF, rfl⟩)))
      rwa [MvPolynomial.eval₂_rename] at this
    · have := h _ (Ideal.subset_span (Or.inr ⟨a, F, hF, rfl⟩))
      rwa [MvPolynomial.eval₂_rename] at this
  · rintro ⟨h₁, h₂, h₃⟩ G hG
    have : segreIdeal I ≤ RingHom.ker (MvPolynomial.eval₂Hom β w) := by
      rw [segreIdeal, Ideal.span_le]
      rintro _ ((⟨a, b, c, d, rfl⟩ | ⟨b, F, hF, rfl⟩) | ⟨a, F, hF, rfl⟩)
      · simp [h₁ a b c d]
      · exact (MvPolynomial.eval₂_rename _ _ _ _).trans (h₂ b F hF)
      · exact (MvPolynomial.eval₂_rename _ _ _ _).trans (h₃ a F hF)
    exact this hG

variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP

theorem box_local {β : R →+* T} {x : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) {w : σ × σ → T}
    (hw : Loc (boxLB M p q) (boxTh th p q) x w) {j k : M.ι} (hj : ∀ y, (x ≫ p) y ∈ M.U j) (hk : ∀ y, (x ≫ q) y ∈ M.U k) :
    ∃ (v₁ v₂ : σ → T) (t : T), IsUnit t ∧ (∀ i, w i = t * (v₁ i.1 * v₂ i.2)) ∧
      (Loc M th (x ≫ p) v₁ ∧ Ideal.span (Set.range v₁) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v₁ F = 0) ∧
      (Loc M th (x ≫ q) v₂ ∧ Ideal.span (Set.range v₂) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v₂ F = 0) := by
  obtain ⟨v₁, h₁⟩ := rep_chart H (x := x ≫ p) (β := β) (by rw [Category.assoc, hx]) hj
  obtain ⟨v₂, h₂⟩ := rep_chart H (x := x ≫ q) (β := β) (by rw [Category.assoc, ← hP.w, hx]) hk
  obtain ⟨t, ht, e⟩ := Loc.unique (DVR.linComb_isLB _ H.1 _ _) (loc_box p q h₁.1 h₂.1) hw (unimod_mul h₁.2.1 h₂.2.1)
  exact ⟨v₁, v₂, t, ht, e, h₁, h₂⟩

theorem box_killed {β : R →+* T} {x : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) {w : σ × σ → T}
    (hw : Loc (boxLB M p q) (boxTh th p q) x w) : Ideal.span (Set.range w) = ⊤ ∧ RankOne I β w := by
  have key : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal,
      Ideal.span (Set.range fun i => algebraMap T (Localization.Away f) (w i)) = ⊤ ∧
      RankOne I ((algebraMap T (Localization.Away f)).comp β) (fun i => algebraMap T (Localization.Away f) (w i)) := by
    intro y
    obtain ⟨j, hj⟩ := exists_chart H.1 ((x ≫ p) y)
    obtain ⟨k, hk⟩ := exists_chart H.1 ((x ≫ q) y)
    obtain ⟨f, hf, hW⟩ := exists_away ((x ≫ p) ⁻¹ᵁ M.U j ⊓ (x ≫ q) ⁻¹ᵁ M.U k) y ⟨hj, hk⟩
    obtain ⟨v₁, v₂, t, ht, e, h₁, h₂⟩ := box_local H hP (β := (algebraMap T (Localization.Away f)).comp β)
      (by rw [Category.assoc, hx, ← spMap_comp]) (hw.baseChange (algebraMap T (Localization.Away f)))
      (fun z => (hW z).1) (fun z => (hW z).2)
    refine ⟨f, hf, ?_, fun a b c d => ?_, fun b F hF => ?_, fun a F hF => ?_⟩
    · rw [funext e]; exact unimod_smul (unimod_mul h₁.2.1 h₂.2.1) ht
    · simp only [e]; ring
    · rw [← rep_smul H h₁.2.1 h₁.2.2 (t * v₂ b) F hF]
      congr 1; funext i; simp only [e]; ring
    · rw [← rep_smul H h₂.2.1 h₂.2.2 (t * v₁ a) F hF]
      congr 1; funext i; simp only [e]; ring
  refine ⟨eq_top_of_away fun y => ?_, fun a b c d => eq_of_away fun y => ?_, fun b F hF => eq_of_away fun y => ?_,
    fun a F hF => eq_of_away fun y => ?_⟩ <;> obtain ⟨f, hf, h₀, h₁, h₂, h₃⟩ := key y <;> refine ⟨f, hf, ?_⟩
  · rw [← span_map, h₀]
  · simpa only [map_mul] using h₁ a b c d
  · rw [MvPolynomial.eval₂_comp_left, map_zero]; exact h₂ b F hF
  · rw [MvPolynomial.eval₂_comp_left, map_zero]; exact h₃ a F hF

theorem box_unique {β : R →+* T} {x x' : Sp T ⟶ Y} (hx : x ≫ p ≫ s = spMap β) (hx' : x' ≫ p ≫ s = spMap β)
    {w : σ × σ → T} (hw : Loc (boxLB M p q) (boxTh th p q) x w) (hw' : Loc (boxLB M p q) (boxTh th p q) x' w) :
    x = x' := by
  refine hom_ext_away fun y => ?_
  obtain ⟨j, hj⟩ := exists_chart H.1 ((x ≫ p) y)
  obtain ⟨k, hk⟩ := exists_chart H.1 ((x ≫ q) y)
  obtain ⟨j', hj'⟩ := exists_chart H.1 ((x' ≫ p) y)
  obtain ⟨k', hk'⟩ := exists_chart H.1 ((x' ≫ q) y)
  obtain ⟨f, hf, hW⟩ := exists_away (((x ≫ p) ⁻¹ᵁ M.U j ⊓ (x ≫ q) ⁻¹ᵁ M.U k) ⊓
    ((x' ≫ p) ⁻¹ᵁ M.U j' ⊓ (x' ≫ q) ⁻¹ᵁ M.U k')) y ⟨⟨hj, hk⟩, hj', hk'⟩
  refine ⟨f, hf, ?_⟩
  have b : (spMap (algebraMap T (Localization.Away f)) ≫ x) ≫ p ≫ s =
      spMap ((algebraMap T (Localization.Away f)).comp β) := by rw [Category.assoc, hx, ← spMap_comp]
  have b' : (spMap (algebraMap T (Localization.Away f)) ≫ x') ≫ p ≫ s =
      spMap ((algebraMap T (Localization.Away f)).comp β) := by rw [Category.assoc, hx', ← spMap_comp]
  obtain ⟨v₁, v₂, t, ht, e, h₁, h₂⟩ := box_local H hP b (hw.baseChange (algebraMap T (Localization.Away f)))
    (fun z => (hW z).1.1) (fun z => (hW z).1.2)
  obtain ⟨w₁, w₂, t', ht', e', k₁, k₂⟩ := box_local H hP b' (hw'.baseChange (algebraMap T (Localization.Away f)))
    (fun z => (hW z).2.1) (fun z => (hW z).2.2)
  obtain ⟨t', rfl⟩ := ht'
  have ee : ∀ i j, w₁ i * w₂ j = ((t'⁻¹).val * t) * (v₁ i * v₂ j) := fun i j => by
    rw [mul_assoc, ← e (i, j), e' (i, j), Units.inv_mul_cancel_left]
  obtain ⟨u₁, hu₁, e₁⟩ := exists_unit_of_mul_eq k₁.2.1 k₂.2.1 ee
  obtain ⟨u₂, hu₂, e₂⟩ := exists_unit_of_mul_eq (v₁ := v₂) (v₂ := v₁) (t := (t'⁻¹).val * t) k₂.2.1 k₁.2.1
    fun i j => by rw [mul_comm, ee, mul_comm (v₂ i)]
  refine hP.hom_ext (rep_unique H ((Category.assoc _ _ _).trans b) ((Category.assoc _ _ _).trans b') k₁.2.1 ?_ k₁.1)
    (rep_unique H (β := (algebraMap T (Localization.Away f)).comp β) (by rw [Category.assoc, ← hP.w, b])
      (by rw [Category.assoc, ← hP.w, b']) k₂.2.1 ?_ k₂.1)
  · rw [funext e₁]; exact h₁.1.smul hu₁
  · rw [funext e₂]; exact h₂.1.smul hu₂

theorem box_exists_unit {β : R →+* T} {w : σ × σ → T} (hw : RankOne I β w) {i : σ × σ} (hi : IsUnit (w i)) :
    ∃ x : Sp T ⟶ Y, x ≫ p ≫ s = spMap β ∧ Loc (boxLB M p q) (boxTh th p q) x w := by
  obtain ⟨a, b⟩ := i
  obtain ⟨x₁, ⟨hx₁, h₁⟩, -⟩ := H.2.2 T β (fun i => w (i, b))
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) hi) (hw.2.1 b)
  obtain ⟨x₂, ⟨hx₂, h₂⟩, -⟩ := H.2.2 T β (fun i => w (a, i))
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨b, rfl⟩) hi) (hw.2.2 a)
  refine ⟨hP.lift x₁ x₂ (hx₁.trans hx₂.symm), by rw [hP.lift_fst_assoc, hx₁], ?_⟩
  obtain ⟨u, hu⟩ := hi
  have := (loc_box p q (x := hP.lift x₁ x₂ (hx₁.trans hx₂.symm)) (by rw [hP.lift_fst]; exact loc_of_secCoord h₁)
    (by rw [hP.lift_snd]; exact loc_of_secCoord h₂)).smul (u⁻¹).isUnit
  convert this using 2 with i
  rw [hw.1 i.1 b a i.2, ← hu, mul_comm (w _), Units.inv_mul_cancel_left]

omit H hP in
theorem RankOne.map {β : R →+* T} {w : σ × σ → T} (hw : RankOne I β w) (φ : T →+* T') :
    RankOne I (φ.comp β) (fun i => φ (w i)) := by
  refine ⟨fun a b c d => by simp only [← map_mul, hw.1 a b c d], fun b F hF => ?_, fun a F hF => ?_⟩
  · have := MvPolynomial.eval₂_comp_left φ β (fun i => w (i, b)) F
    rw [hw.2.1 b F hF, map_zero] at this
    exact this.symm
  · have := MvPolynomial.eval₂_comp_left φ β (fun i => w (a, i)) F
    rw [hw.2.2 a F hF, map_zero] at this
    exact this.symm

theorem box_exists {β : R →+* T} {w : σ × σ → T} (hs : Ideal.span (Set.range w) = ⊤) (hw : RankOne I β w) :
    ∃ x : Sp T ⟶ Y, x ≫ p ≫ s = spMap β ∧ Loc (boxLB M p q) (boxTh th p q) x w := by
  choose x hx hl using fun i : σ × σ => box_exists_unit H hP (hw.map (algebraMap T (Localization.Away (w i))))
    (i := i) (IsLocalization.Away.algebraMap_isUnit _)
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of T) w hs).openCover
  have hc : ∀ i j : σ × σ, pullback.fst (𝒰.f i) (𝒰.f j) ≫ x i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ x j := by
    intro i j
    let A := Localization.Away (w i)
    let B := Localization.Away (w j)
    refine (cancel_epi (pullbackSpecIso T A B).inv).1 ?_
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (congrArg (· ≫ x i) (pullbackSpecIso_inv_fst T A B)).trans
      (Eq.trans ?_ (congrArg (· ≫ x j) (pullbackSpecIso_inv_snd T A B)).symm)
    let l : A →+* A ⊗[T] B := Algebra.TensorProduct.includeLeftRingHom
    let r : B →+* A ⊗[T] B := (Algebra.TensorProduct.includeRight (R := T) (A := A) (B := B)).toRingHom
    have e : l.comp (algebraMap T A) = r.comp (algebraMap T B) :=
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
    show spMap l ≫ x i = spMap r ≫ x j
    refine box_unique H hP (β := (l.comp (algebraMap T A)).comp β) ?_ ?_ ((hl i).baseChange l) ?_
    · rw [Category.assoc, hx, ← spMap_comp, RingHom.comp_assoc]
    · rw [Category.assoc, hx, ← spMap_comp, e, RingHom.comp_assoc]
    · convert (hl j).baseChange r using 2 with k
      exact congrArg (fun φ : T →+* A ⊗[T] B => φ (w k)) e
  have hg : ∀ i : σ × σ, spMap (algebraMap T (Localization.Away (w i))) ≫ 𝒰.glueMorphisms x hc = x i :=
    fun i => 𝒰.ι_glueMorphisms x hc i
  refine ⟨𝒰.glueMorphisms x hc, 𝒰.hom_ext _ _ fun i => ?_, loc_of_away fun y => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p ≫ s) (hg i)).trans ((hx i).trans (spMap_comp _ _)))
  · obtain ⟨i, hi⟩ : ∃ i, w i ∉ y.asIdeal := by
      by_contra hn
      push Not at hn
      exact y.isPrime.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hn i)))
    exact ⟨w i, hi, by rw [hg]; exact hl i⟩

theorem projRep_box : ProjRep (segreIdeal I) (p ≫ s) (boxLB M p q) (boxTh th p q) := by
  refine ⟨DVR.linComb_isLB _ H.1 _ _, fun T _ β x w hx hw => ?_, fun T _ β w hs hw => ?_⟩
  · obtain ⟨h₁, h₂⟩ := box_killed H hP hx (loc_of_secCoord hw)
    exact ⟨h₁, (killed_iff I β w).2 h₂⟩
  · obtain ⟨x, hx, hl⟩ := box_exists H hP hs ((killed_iff I β w).1 hw)
    exact ⟨x, ⟨hx, secCoord_of_loc hs hl⟩, fun x' h' => box_unique H hP h'.1 hx (loc_of_secCoord h'.2) hl⟩

theorem secCoord_box (x : Sp T ⟶ Y) (v₁ v₂ : σ → T) (h₁ : SecCoord M th (x ≫ p) v₁) (h₂ : SecCoord M th (x ≫ q) v₂) :
    SecCoord (boxLB M p q) (boxTh th p q) x (fun i => v₁ i.1 * v₂ i.2) := by
  have hl := loc_box p q (loc_of_secCoord h₁) (loc_of_secCoord h₂)
  have hx : x ≫ p ≫ s = spMap (Spec.preimage (x ≫ p ≫ s)).hom := (Spec.map_preimage _).symm
  exact secCoord_of_loc (box_killed H hP hx hl).1 hl

end Segre

theorem exists_segre_coordinates : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → ∃ (I₂ : Ideal (MvPolynomial (σ × σ) R)) (M₂ : LB (Z ⊗ Z).left) (th₂ : σ × σ → M₂.Sec), ProjRep I₂ (Z ⊗ Z).hom M₂ th₂ ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ (Z ⊗ Z).left) (v₁ v₂ : σ → T), SecCoord M th (x ≫ (fst Z Z).left) v₁ → SecCoord M th (x ≫ (snd Z Z).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2) := by
  intro R σ _ _ I Z M th H
  have hP : IsPullback (fst Z Z).left (snd Z Z).left Z.hom Z.hom := IsPullback.of_hasPullback Z.hom Z.hom
  refine ⟨segreIdeal I, boxLB M (fst Z Z).left (snd Z Z).left, boxTh th (fst Z Z).left (snd Z Z).left, ?_,
    fun T _ x v₁ v₂ h₁ h₂ => secCoord_box H hP x v₁ v₂ h₁ h₂⟩
  rw [← Over.w (fst Z Z)]
  exact projRep_box H hP

end GlobalTheory.SegreCoord
end
