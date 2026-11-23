import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG valR lbPow LBIso)
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open GlobalTheory.QCoh.Qcqs GlobalTheory.ProjSpace GlobalTheory.Points

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.TuplePoint

variable {L : Type} [Field L] {X Y : Scheme.{0}}

theorem le_preimage_of_mem (η : Sp L ⟶ X) [IsDominant η] {W : X.Opens} {x : X} (hx : x ∈ W) :
    ⊤ ≤ η ⁻¹ᵁ W := by
  obtain ⟨q, hq⟩ := η.denseRange.exists_mem_open W.isOpen ⟨x, hx⟩
  intro p _
  obtain rfl : p = q := Subsingleton.elim (α := PrimeSpectrum L) p q
  exact hq

theorem ext_of_dense (η : Sp L ⟶ X) [IsDominant η] [IsReduced X] {W : X.Opens} {s s' : Γ(X, W)}
    (h : ⊤ ≤ η ⁻¹ᵁ W → valR η W s = valR η W s') : s = s' := by
  have key : X.basicOpen (s - s') = ⊥ := by
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
    have hW : ⊤ ≤ η ⁻¹ᵁ W := le_preimage_of_mem η (X.basicOpen_le _ hy)
    have hB := le_preimage_of_mem η hy
    rw [le_preimage_basicOpen_iff η hW, sub_eq_add_neg, valR_add η W hW, valR_neg η W hW, h hW,
      add_neg_cancel] at hB
    exact not_isUnit_zero hB
  exact sub_eq_zero.mp ((basicOpen_eq_bot_iff _).mp key)

theorem valMap_injective (η : Sp L ⟶ X) [IsDominant η] [IsReduced X] {W : X.Opens}
    (h : ⊤ ≤ η ⁻¹ᵁ W) : Function.Injective (valMap η W h).hom := by
  intro s s' hss
  exact ext_of_dense η fun _ => by rw [valR_eq η W h, valR_eq η W h]; exact hss

variable {o : Type} [CommRing o] [Algebra o L]

theorem valMap_baseRingHom {η : Sp L ⟶ X} {f : X ⟶ Sp o} (hf : η ≫ f = spMap (algebraMap o L))
    {W : X.Opens} (h : ⊤ ≤ η ⁻¹ᵁ W) (a : o) :
    (valMap η W h).hom ((baseRingHom f W).hom a) = algebraMap o L a := by
  rw [← valR_eq η W h]
  exact valR_constFn_of_over f (algebraMap o L) η hf W h a

theorem valMap_eval₂Hom {σ : Type*} {η : Sp L ⟶ X} {f : X ⟶ Sp o}
    (hf : η ≫ f = spMap (algebraMap o L)) {W : X.Opens} (h : ⊤ ≤ η ⁻¹ᵁ W) (u : σ → Γ(X, W))
    (p : MvPolynomial σ o) :
    (valMap η W h).hom (eval₂Hom (baseRingHom f W).hom u p) =
      aeval (fun k => valR η W (u k)) p := by
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.aeval_def]
  have hc : (valMap η W h).hom.comp (baseRingHom f W).hom = algebraMap o L :=
    RingHom.ext (valMap_baseRingHom hf h)
  have hv : (fun k => (valMap η W h).hom (u k)) = fun k => valR η W (u k) :=
    funext fun k => (valR_eq η W h (u k)).symm
  rw [hc, hv, MvPolynomial.coe_eval₂Hom]

variable {r M : ℕ}

theorem map_irrelevant_eq_top (o : Type) [CommRing o] [Algebra o L] {t : Fin (r + 1) → L}
    (ht : t ≠ 0) : (HomogeneousIdeal.irrelevant (grading o r)).toIdeal.map
      (aeval (R := o) t).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ht
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem o r i))) ?_
  simpa using hi

def point (o : Type) [CommRing o] [Algebra o L] (t : Fin (r + 1) → L) (ht : t ≠ 0) :
    Sp L ⟶ PSpace o r :=
  ProjPoint.ofHom (grading o r) (aeval (R := o) t).toRingHom (map_irrelevant_eq_top o ht)

variable {t : Fin (r + 1) → L} {ht : t ≠ 0}

@[reassoc]
theorem point_str : point o t ht ≫ PSpace.str o r = spMap (algebraMap o L) := by
  simp only [point, PSpace.str, spMap, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  ext a
  simp

theorem le_point_preimage_iff (i : Fin (r + 1)) :
    ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i ↔ t i ≠ 0 := by
  rw [point, ProjPoint.ofHom_preimage_basicOpen _ _ _ Nat.one_pos (X_mem o r i)]
  show (⊤ : Opens (PrimeSpectrum L)) ≤ PrimeSpectrum.basicOpen ((aeval t).toRingHom (X i)) ↔ _
  constructor
  · intro hle h0
    have hm := hle (show (default : PrimeSpectrum L) ∈ (⊤ : Opens (PrimeSpectrum L)) from trivial)
    rw [PrimeSpectrum.mem_basicOpen] at hm
    apply hm
    simp [h0]
  · intro h1 p _
    rw [PrimeSpectrum.mem_basicOpen, Ideal.eq_bot_of_prime p.asIdeal]
    simpa using h1

theorem valR_point_ratio {i : Fin (r + 1)} (hi : t i ≠ 0) (j : Fin (r + 1)) :
    valR (point o t ht) (chart o r i) (ratio o r i j) = t j / t i := by
  have hu : IsUnit ((aeval t).toRingHom (X i : MvPolynomial (Fin (r + 1)) o)) := by simpa using hi
  have hpre : ⊤ ≤ Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos ⁻¹ᵁ chart o r i := by
    have e1 := Scheme.Hom.preimage_opensRange
      (Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos)
    rw [Proj.opensRange_awayι] at e1
    exact e1.ge
  have hmem : (X j : MvPolynomial (Fin (r + 1)) o) ∈ grading o r (1 • 1) := by
    simpa using X_mem o r j
  have hA : ratio o r i j = (Proj.awayToSection (grading o r) (X i)).hom
      (HomogeneousLocalization.Away.mk (grading o r) (X_mem o r i) 1 (X j) hmem) := by
    rw [ProjFrac.awayToSection_mk]
    exact ProjFrac.frac_eq (by ring)
  have key : Proj.awayToSection (grading o r) (X i) ≫
      (Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos).appLE (chart o r i) ⊤ hpre =
      (Scheme.ΓSpecIso _).inv := by
    set A := Proj.awayι (grading o r) (X i) (X_mem o r i) Nat.one_pos
    set e := Proj.basicOpenIsoSpec (grading o r) (X i) (X_mem o r i) Nat.one_pos
    have : IsIso (Proj.awayToSection (grading o r) (X i)) :=
      (Proj.basicOpenIsoAway (grading o r) (X i) (X_mem o r i) Nat.one_pos).isIso_hom
    have hι : e.hom ≫ A = (chart o r i).ι := by
      exact Iso.hom_inv_id_assoc e _
    have gen : ∀ (g : (chart o r i).toScheme ⟶ Proj (grading o r)) (_ : e.hom ≫ A = g)
        (hle : ⊤ ≤ g ⁻¹ᵁ chart o r i),
        g.appLE (chart o r i) ⊤ hle = A.appLE (chart o r i) ⊤ hpre ≫ e.hom.appLE ⊤ ⊤ le_rfl := by
      rintro g rfl hle
      exact (Scheme.Hom.appLE_comp_appLE e.hom A (chart o r i) ⊤ ⊤ hpre _).symm
    have h1 := gen _ hι (chart o r i).ι_preimage_self.ge
    have F1 : e.hom.appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫
        Proj.awayToSection (grading o r) (X i) ≫ (chart o r i).topIso.inv := by
      rw [← Proj.basicOpenToSpec_app_top]
      rfl
    have F2 : (chart o r i).ι.appLE (chart o r i) ⊤ (chart o r i).ι_preimage_self.ge =
        (chart o r i).topIso.inv := by
      rw [Scheme.Opens.ι_appLE]
      rfl
    rw [F2, F1] at h1
    have h3 : A.appLE (chart o r i) ⊤ hpre ≫ (Scheme.ΓSpecIso _).hom ≫
        Proj.awayToSection (grading o r) (X i) = 𝟙 _ := by
      rw [← cancel_mono (chart o r i).topIso.inv, Category.id_comp, Category.assoc, Category.assoc]
      exact h1.symm
    rw [← cancel_mono ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading o r) (X i)),
      Category.assoc, h3, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [point, ProjPoint.ofHom_eq_awayι _ _ _ Nat.one_pos (X_mem o r i) hu,
    ← valR_appLE _ _ hpre (le_preimage_top _), hA, ← CommRingCat.comp_apply, key, valR_specMap]
  apply eq_div_of_mul_eq hi
  simpa using ProjPoint.awayLift_mk_mul (grading o r) ((aeval t).toRingHom) hu (X_mem o r i) 1 (X j) hmem

theorem eq_point {x : Sp L ⟶ PSpace o r} (hx : x ≫ PSpace.str o r = spMap (algebraMap o L))
    {i : Fin (r + 1)} (hi : t i ≠ 0) (h : ⊤ ≤ x ⁻¹ᵁ chart o r i)
    (hv : ∀ j, valR x (chart o r i) (ratio o r i j) = t j / t i) : x = point o t ht := by
  refine ProjSpace.hom_ext (hx.trans point_str.symm) fun _ =>
    ⟨⊤, by simp, i, h, (le_point_preimage_iff i).mpr hi, fun j => ?_⟩
  have h1 : ⊤ ≤ (𝟙 (Sp L)) ⁻¹ᵁ (⊤ : (Sp L).Opens) := le_preimage_top _
  apply valMap_injective (𝟙 (Sp L)) h1
  rw [← valR_eq, ← valR_eq, pullRatio, pullRatio, valR_appLE (𝟙 _) x h h1,
    valR_appLE (𝟙 _) (point o t ht) _ h1, Category.id_comp, Category.id_comp, hv j,
    valR_point_ratio hi]

theorem range_valMap_point {i : Fin (r + 1)} (h : ⊤ ≤ point o t ht ⁻¹ᵁ chart o r i) :
    Set.range (valMap (point o t ht) _ h).hom =
      Algebra.adjoin o (Set.range fun k => t k / t i) := by
  have hi : t i ≠ 0 := (le_point_preimage_iff i).mp h
  have hc : ∀ a : o, (valMap (point o t ht) _ h).hom (algebraMap o Γ(PSpace o r, chart o r i) a) =
      algebraMap o L a :=
    valMap_baseRingHom point_str h
  have hr : ∀ k, (valMap (point o t ht) _ h).hom (ratio o r i k) = t k / t i := fun k => by
    rw [← valR_eq, valR_point_ratio hi]
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨p, rfl⟩ := (chartAlgEquiv o r i).surjective f
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, hc]
      exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, map_mul, chartAlgEquiv_X, hr]
      exact mul_mem hp (Algebra.subset_adjoin ⟨j.1, rfl⟩)
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨ratio o r i k, hr k⟩
    | algebraMap a => exact ⟨_, hc a⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f + g, map_add _ f g⟩
    | mul x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨g, rfl⟩ := hy
      exact ⟨f * g, map_mul _ f g⟩

section

variable {η : Sp L ⟶ X} {π : X ⟶ PSpace o r} (hπ : η ≫ π = point o t ht)

include hπ

theorem ne_zero_of_le {W : X.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {i : Fin (r + 1)}
    (hi : W ≤ π ⁻¹ᵁ chart o r i) : t i ≠ 0 := by
  have key := le_preimage_comp η π hi hW
  rw [hπ, le_point_preimage_iff] at key
  exact key

theorem le_preimage_chart {i : Fin (r + 1)} (hi : t i ≠ 0) : ⊤ ≤ η ⁻¹ᵁ (π ⁻¹ᵁ chart o r i) := by
  have key := (le_point_preimage_iff (o := o) (ht := ht) i).mpr hi
  rw [← hπ] at key
  exact key

theorem valR_pullRatio {W : X.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {i : Fin (r + 1)}
    (hi : W ≤ π ⁻¹ᵁ chart o r i) (j : Fin (r + 1)) :
    valR η W (pullRatio π W i hi j) = t j / t i := by
  rw [pullRatio, valR_appLE η π hi hW, hπ, valR_point_ratio (ne_zero_of_le hπ hW hi)]

end

theorem exists_hom_of_coords [IsReduced X] (η : Sp L ⟶ X) [IsDominant η] (f : X ⟶ Sp o)
    (hf : η ≫ f = spMap (algebraMap o L)) {ι : Type} (U : ι → X.Opens) (hU : ⨆ a, U a = ⊤)
    (hη : ∀ a, ⊤ ≤ η ⁻¹ᵁ U a) {z : Fin (M + 1) → L} (hz : z ≠ 0) (c : ι → Fin (M + 1))
    (hc : ∀ a, z (c a) ≠ 0) (u : ∀ a, Fin (M + 1) → Γ(X, U a))
    (hu : ∀ a k, valR η (U a) (u a k) = z k / z (c a)) :
    ∃ φ : X ⟶ PSpace o M, η ≫ φ = point o z hz ∧ φ ≫ PSpace.str o M = f ∧
      ∀ a, U a ≤ φ ⁻¹ᵁ chart o M (c a) := by
  have hone : ∀ a, u a (c a) = 1 := fun a =>
    ext_of_dense η fun h => by rw [hu a, div_self (hc a), valR_one η _ h]
  have hrel : ∀ a b k, resG X (inf_le_left : U a ⊓ U b ≤ U a) (u a k) =
      resG X (inf_le_left : U a ⊓ U b ≤ U a) (u a (c b)) *
        resG X (inf_le_right : U a ⊓ U b ≤ U b) (u b k) := by
    intro a b k
    apply ext_of_dense η
    intro h
    rw [valR_mul η _ h, valR_res η inf_le_left h, valR_res η inf_le_left h, valR_res η inf_le_right h,
      hu, hu, hu]
    field_simp [hc a, hc b]
  have compat : ∀ (a b : ι) {Z : Scheme.{0}} (p : Z ⟶ (U a).toScheme) (q : Z ⟶ (U b).toScheme),
      p ≫ (U a).ι = q ≫ (U b).ι →
        p ≫ ofCoords f (U a) (c a) (u a) = q ≫ ofCoords f (U b) (c b) (u b) := by
    intro a b Z p q hpq
    have hA : ⊤ ≤ (p ≫ (U a).ι) ⁻¹ᵁ U a := fun x _ => (p.base x).2
    have hB : ⊤ ≤ (q ≫ (U b).ι) ⁻¹ᵁ U b := fun x _ => (q.base x).2
    have hB' : ⊤ ≤ (p ≫ (U a).ι) ⁻¹ᵁ U b := by rw [hpq]; exact hB
    have hAB : ⊤ ≤ (p ≫ (U a).ι) ⁻¹ᵁ (U a ⊓ U b) := le_inf hA hB'
    have pb : ∀ k, ((p ≫ (U a).ι).appLE (U a ⊓ U b) ⊤ hAB).hom (resG X inf_le_right (u b k)) =
        ((q ≫ (U b).ι).appLE (U b) ⊤ hB).hom (u b k) := fun k => by
      rw [appLE_resG, appLE_of_eq hpq (U b) ⊤ _ hB]
    have rel : ∀ k, ((p ≫ (U a).ι).appLE (U a) ⊤ hA).hom (u a k) =
        ((p ≫ (U a).ι).appLE (U a) ⊤ hA).hom (u a (c b)) *
          ((q ≫ (U b).ι).appLE (U b) ⊤ hB).hom (u b k) := fun k => by
      have e := congrArg ((p ≫ (U a).ι).appLE (U a ⊓ U b) ⊤ hAB).hom (hrel a b k)
      rw [map_mul, pb, appLE_resG, appLE_resG] at e
      exact e
    have inv1 : ((p ≫ (U a).ι).appLE (U a) ⊤ hA).hom (u a (c b)) *
        ((q ≫ (U b).ι).appLE (U b) ⊤ hB).hom (u b (c a)) = 1 := by
      rw [← rel, hone a, map_one]
    have hpa := ofCoords_preimage f (U a) (c a) (u a) p
    have hqb := ofCoords_preimage f (U b) (c b) (u b) q
    have ra : ∀ k, pullRatio (p ≫ ofCoords f (U a) (c a) (u a)) ⊤ (c a) hpa k =
        ((p ≫ (U a).ι).appLE (U a) ⊤ hA).hom (u a k) :=
      fun k => pullRatio_comp_ofCoords f (U a) (c a) (hone a) p ⊤ hpa hA k
    have rb : ∀ k, pullRatio (q ≫ ofCoords f (U b) (c b) (u b)) ⊤ (c b) hqb k =
        ((q ≫ (U b).ι).appLE (U b) ⊤ hB).hom (u b k) :=
      fun k => pullRatio_comp_ofCoords f (U b) (c b) (hone b) q ⊤ hqb hB k
    have h2 : ⊤ ≤ (q ≫ ofCoords f (U b) (c b) (u b)) ⁻¹ᵁ chart o M (c a) := by
      have hu' : IsUnit (pullRatio (q ≫ ofCoords f (U b) (c b) (u b)) ⊤ (c b) hqb (c a)) := by
        rw [rb]
        exact ⟨⟨_, _, (mul_comm _ _).trans inv1, inv1⟩, rfl⟩
      have e := basicOpen_pullRatio (φ := q ≫ ofCoords f (U b) (c b) (u b)) (W := ⊤) (i := c b)
        (hi := hqb) (j := c a)
      rw [Scheme.basicOpen_of_isUnit _ hu', top_inf_eq] at e
      exact e.le
    refine ProjSpace.hom_ext ?_ fun _ => ⟨⊤, by simp, c a, hpa, h2, fun j => ?_⟩
    · rw [Category.assoc, Category.assoc, ofCoords_str, ofCoords_str, ← Category.assoc, hpq,
        Category.assoc]
    · have m1 := pullRatio_mul_pullRatio (φ := q ≫ ofCoords f (U b) (c b) (u b)) (W := ⊤)
        (i := c a) (j := c b) (k := j) (hi := h2) (hj := hqb)
      have m2 := pullRatio_mul_pullRatio (φ := q ≫ ofCoords f (U b) (c b) (u b)) (W := ⊤)
        (i := c b) (j := c a) (k := c b) (hi := hqb) (hj := h2)
      rw [pullRatio_self, rb] at m2
      rw [rb] at m1
      have hx : pullRatio (q ≫ ofCoords f (U b) (c b) (u b)) ⊤ (c a) h2 (c b) =
          ((p ≫ (U a).ι).appLE (U a) ⊤ hA).hom (u a (c b)) := by
        rw [← mul_one (pullRatio _ _ _ h2 (c b)), ← inv1, mul_comm, mul_assoc, m2, mul_one]
      rw [ra, rel j, ← m1, hx]
  let g : X ⟶ PSpace o M := (X.openCoverOfIsOpenCover U hU).glueMorphisms
    (fun a => ofCoords f (U a) (c a) (u a)) fun a b => compat a b _ _ pullback.condition
  have hg : ∀ a, (U a).ι ≫ g = ofCoords f (U a) (c a) (u a) := fun a =>
    (X.openCoverOfIsOpenCover U hU).ι_glueMorphisms _ _ a
  have hpre : ∀ a, U a ≤ g ⁻¹ᵁ chart o M (c a) := fun a x hx => by
    have h := ofCoords_preimage_top f (U a) (c a) (u a)
      (show (⟨x, hx⟩ : (U a).toScheme) ∈ (⊤ : (U a).toScheme.Opens) from trivial)
    rw [← hg a] at h
    exact h
  have hratio : ∀ a j, pullRatio g (U a) (c a) (hpre a) j = u a j := by
    intro a j
    apply (ConcreteCategory.bijective_of_isIso ((U a).ι.appLE (U a) ⊤ (U a).ι_preimage_self.ge)).1
    rw [appLE_pullRatio, pullRatio_of_eq ((hg a).trans (Category.id_comp _).symm) _
      (ofCoords_preimage f (U a) (c a) (u a) (𝟙 _)),
      pullRatio_comp_ofCoords f (U a) (c a) (hone a) (𝟙 _) ⊤ _ (by simp), appLE_of_eq (Category.id_comp _)]
  have hstr : g ≫ PSpace.str o M = f :=
    (X.openCoverOfIsOpenCover U hU).hom_ext _ _ fun a => by
      rw [← Category.assoc]
      exact (congrArg (· ≫ PSpace.str o M) (hg a)).trans (ofCoords_str f (U a) (c a) (u a))
  obtain ⟨a0, ha0⟩ := exists_le_preimage_of_iSup_eq_top η hU
  refine ⟨g, ?_, hstr, hpre⟩
  refine eq_point (by rw [Category.assoc, hstr, hf]) (hc a0) (le_preimage_comp η g (hpre a0) ha0)
    fun j => ?_
  rw [← valR_appLE η g (hpre a0) ha0]
  exact (congrArg (valR η (U a0)) (hratio a0 j)).trans (hu a0 j)

theorem isClosedImmersion_of_cover (φ : X ⟶ Y) (hcl : IsClosed (Set.range φ)) {ι : Type}
    (V : ι → Y.Opens) (hV : ∀ a, IsAffineOpen (V a)) (hU : ∀ a, IsAffineOpen (φ ⁻¹ᵁ V a))
    (hs : ∀ a, Function.Surjective (φ.app (V a)).hom) (hc : ⨆ a, φ ⁻¹ᵁ V a = ⊤) :
    IsClosedImmersion φ := by
  let W : Option ι → Y.Opens := fun a => a.elim ⟨(Set.range φ)ᶜ, hcl.isOpen_compl⟩ V
  have hW : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range φ
    · obtain ⟨x, rfl⟩ := hy
      have hx : x ∈ ⨆ a, φ ⁻¹ᵁ V a := by rw [hc]; trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨some a, ha⟩
    · exact ⟨none, hy⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun a => ?_
  cases a with
  | none =>
    have : IsEmpty (φ ⁻¹ᵁ W none).toScheme := ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
    infer_instance
  | some a =>
    have : IsAffine (V a).toScheme := hV a
    have : IsAffine (φ ⁻¹ᵁ V a).toScheme := hU a
    show IsClosedImmersion (φ ∣_ V a)
    apply IsClosedImmersion.of_surjective_of_isAffine
    rw [morphismRestrict_appTop]
    have key : ∀ Z (_ : Z = V a), Function.Surjective (φ.app Z).hom := by
      rintro _ rfl
      exact hs a
    exact (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage φ (V a) ⊤)).op)).2.comp
        (key _ (V a).ι_image_top)

section Units

variable (η : Sp L ⟶ X) {U V : X.Opens}

theorem valR_res_unit (e : V ≤ U) (h : ⊤ ≤ η ⁻¹ᵁ V) (u : Γ(X, U)ˣ) :
    valR η V (res e u).val = valR η U u.val := valR_res η e h u.val

theorem valR_pullU (g : X ⟶ Y) (W : Y.Opens) (u : Γ(Y, W)ˣ) :
    valR η (g ⁻¹ᵁ W) (pullU g W u).val = valR (η ≫ g) W u.val := (valR_comp η g W u.val).symm

theorem valR_mul_unit (h : ⊤ ≤ η ⁻¹ᵁ U) (u v : Γ(X, U)ˣ) :
    valR η U (u * v).val = valR η U u.val * valR η U v.val := by
  rw [Units.val_mul]
  exact valR_mul η U h _ _

theorem valR_zpow_unit (h : ⊤ ≤ η ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valR η U (u ^ n).val = valR η U u.val ^ n := by
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, valR_pow η U h]
  · have key := valR_mul η U h (u ^ (k + 1)).val ((u ^ (k + 1))⁻¹).val
    rw [Units.mul_inv, valR_one η U h] at key
    rw [zpow_negSucc, eq_inv_of_mul_eq_one_right key.symm, Units.val_pow_eq_pow_val,
      valR_pow η U h, zpow_negSucc]

theorem valR_inv_unit (h : ⊤ ≤ η ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valR η U (u⁻¹).val = (valR η U u.val)⁻¹ := by
  have key := valR_mul η U h u.val (u⁻¹).val
  rw [Units.mul_inv, valR_one η U h] at key
  exact eq_inv_of_mul_eq_one_right key.symm

theorem valR_linComb_g (B : LB Y) (g : X ⟶ Y) (n : ℤ) (i j : PUnit → B.ι)
    (h : ⊤ ≤ η ⁻¹ᵁ (LB.wchart B (fun _ => g) i ⊓ LB.wchart B (fun _ => g) j)) :
    valR η (LB.wchart B (fun _ => g) i ⊓ LB.wchart B (fun _ => g) j)
        ((LB.LinComb B (K := PUnit) (fun _ => g) (fun _ => n)).g i j).val =
      valR (η ≫ g) _ (B.g (i PUnit.unit) (j PUnit.unit)).val ^ n := by
  rw [linComb_punit_g, valR_zpow_unit η h]
  congr 1
  exact (valR_res_unit η _ h _).trans
    (valR_pullU η g (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)) (B.g (i PUnit.unit) (j PUnit.unit)))

end Units

theorem valR_pullback_twistingSheaf_transition {η : Sp L ⟶ X} {π : X ⟶ PSpace o r} (hπ : η ≫ π = point o t ht)
    (i j : PUnit → Fin (r + 1))
    (h : ⊤ ≤ η ⁻¹ᵁ (((O1 o r).pull π).U i ⊓ ((O1 o r).pull π).U j)) :
    valR η (((O1 o r).pull π).U i ⊓ ((O1 o r).pull π).U j) (((O1 o r).pull π).g i j).val =
      t (j PUnit.unit) / t (i PUnit.unit) := by
  have hU : ⊤ ≤ (η ≫ π) ⁻¹ᵁ (chart o r (i PUnit.unit) ⊓ chart o r (j PUnit.unit)) :=
    le_preimage_comp η π (le_inf (inf_le_left.trans (LB.wchart_le (O1 o r) (fun _ => π) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le (O1 o r) (fun _ => π) j PUnit.unit))) h
  have hi : t (i PUnit.unit) ≠ 0 := by
    have key := le_preimage_mono (η ≫ π) inf_le_left hU
    rw [hπ, le_point_preimage_iff] at key
    exact key
  refine (valR_linComb_g η (O1 o r) π 1 i j h).trans ?_
  show valR (η ≫ π) (chart o r (i PUnit.unit) ⊓ chart o r (j PUnit.unit)) _ ^ _ = _
  simp only [zpow_one]
  rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit, ← resG_ratioOn (hi := le_rfl) inf_le_left,
    valR_res (η ≫ π) inf_le_left hU, hπ, valR_point_ratio hi]

theorem exists_iso_lbPow [IsReduced X] {η : Sp L ⟶ X} [IsDominant η] {π : X ⟶ PSpace o r}
    (hπ : η ≫ π = point o t ht) {z : Fin (M + 1) → L} {hz : z ≠ 0} {φ : X ⟶ PSpace o M}
    (hφ : η ≫ φ = point o z hz) {e : ℕ} (c : Fin (r + 1) → Fin (M + 1))
    (hc : ∀ j, z (c j) = t j ^ e) (hle : ∀ j, π ⁻¹ᵁ chart o r j ≤ φ ⁻¹ᵁ chart o M (c j)) :
    ∃ w : LB.Iso (lbPow ((O1 o r).pull π) e) ((O1 o M).pull φ), w.IsGen ∧
      ∀ (k : PUnit → Fin (M + 1)) (j : PUnit → PUnit → Fin (r + 1)),
        ⊤ ≤ η ⁻¹ᵁ (((O1 o M).pull φ).U k ⊓ (lbPow ((O1 o r).pull π) e).U j) →
        valR η _ (w.s (k, j)).val = t (j PUnit.unit PUnit.unit) ^ e / z (k PUnit.unit) := by
  have hsub : ∀ (k : PUnit → Fin (M + 1)) (j : PUnit → PUnit → Fin (r + 1)),
      ((O1 o M).pull φ).U k ⊓ (lbPow ((O1 o r).pull π) e).U j ≤
        φ ⁻¹ᵁ (chart o M (k PUnit.unit) ⊓ chart o M (c (j PUnit.unit PUnit.unit))) := by
    intro k j
    show _ ≤ φ ⁻¹ᵁ chart o M (k PUnit.unit) ⊓ φ ⁻¹ᵁ chart o M (c (j PUnit.unit PUnit.unit))
    apply le_inf
    · exact inf_le_left.trans (LB.wchart_le (O1 o M) (fun _ => φ) k PUnit.unit)
    · exact inf_le_right.trans ((LB.wchart_le ((O1 o r).pull π) (fun _ => 𝟙 X) j PUnit.unit).trans
        ((LB.wchart_le (O1 o r) (fun _ => π) (j PUnit.unit) PUnit.unit).trans (hle _)))
  have key : ∀ (k : PUnit → Fin (M + 1)) (jj : PUnit → PUnit → Fin (r + 1)) (V : X.Opens)
      (hV : ⊤ ≤ η ⁻¹ᵁ V)
      (e1 : V ≤ φ ⁻¹ᵁ (chart o M (k PUnit.unit) ⊓ chart o M (c (jj PUnit.unit PUnit.unit)))),
      valR η V (res e1 (pullU φ _ (ratioUnit _ (k PUnit.unit) (c (jj PUnit.unit PUnit.unit))
        inf_le_left inf_le_right))).val = t (jj PUnit.unit PUnit.unit) ^ e / z (k PUnit.unit) := by
    intro k jj V hV e1
    have hU' : ⊤ ≤ (η ≫ φ) ⁻¹ᵁ (chart o M (k PUnit.unit) ⊓ chart o M (c (jj PUnit.unit PUnit.unit))) :=
      le_preimage_comp η φ e1 hV
    have hk : z (k PUnit.unit) ≠ 0 := by
      have hh := le_preimage_mono (η ≫ φ) inf_le_left hU'
      rw [hφ, le_point_preimage_iff] at hh
      exact hh
    rw [valR_res_unit η e1 hV, valR_pullU, val_ratioUnit, ← resG_ratioOn (hi := le_rfl) inf_le_left,
      valR_res (η ≫ φ) inf_le_left hU', hφ, valR_point_ratio hk, hc]
  refine ⟨{ s := fun i => res (hsub i.1 i.2) (pullU φ _ (ratioUnit _ (i.1 PUnit.unit)
    (c (i.2 PUnit.unit PUnit.unit)) inf_le_left inf_le_right)) }, ?_, ?_⟩
  · intro i j
    apply Units.ext
    dsimp only [LB.div]
    apply ext_of_dense η
    intro h
    have hM : ⊤ ≤ η ⁻¹ᵁ (((O1 o M).pull φ).U i.1 ⊓ ((O1 o M).pull φ).U j.1) :=
      le_preimage_mono η (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) h
    have hL : ⊤ ≤ η ⁻¹ᵁ ((lbPow ((O1 o r).pull π) e).U i.2 ⊓ (lbPow ((O1 o r).pull π) e).U j.2) :=
      le_preimage_mono η (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) h
    have hL' : ⊤ ≤ η ⁻¹ᵁ (((O1 o r).pull π).U (i.2 PUnit.unit) ⊓ ((O1 o r).pull π).U (j.2 PUnit.unit)) :=
      le_preimage_mono η (inf_le_inf (LB.wchart_le ((O1 o r).pull π) (fun _ => 𝟙 X) i.2 PUnit.unit)
        (LB.wchart_le ((O1 o r).pull π) (fun _ => 𝟙 X) j.2 PUnit.unit)) hL
    have hg := valR_linComb_g η ((O1 o r).pull π) (𝟙 X) (e : ℤ) i.2 j.2 hL
    rw [Category.comp_id, valR_pullback_twistingSheaf_transition hπ _ _ hL', zpow_natCast] at hg
    have hgM := valR_pullback_twistingSheaf_transition hφ i.1 j.1 hM
    have hzj : z (j.1 PUnit.unit) ≠ 0 := by
      have hh := le_preimage_comp η φ (LB.wchart_le (O1 o M) (fun _ => φ) j.1 PUnit.unit)
        (le_preimage_mono η inf_le_right hM)
      rw [hφ] at hh
      exact (le_point_preimage_iff _).mp hh
    have htj : ∀ q : PUnit → PUnit → Fin (r + 1), ⊤ ≤ η ⁻¹ᵁ ((O1 o r).pull π).U (q PUnit.unit) →
        t (q PUnit.unit PUnit.unit) ≠ 0 := fun q hq => by
      have hh := le_preimage_comp η π (LB.wchart_le (O1 o r) (fun _ => π) (q PUnit.unit) PUnit.unit) hq
      rw [hπ] at hh
      exact (le_point_preimage_iff _).mp hh
    have ht1 := htj i.2 (le_preimage_mono η inf_le_left hL')
    have ht2 := htj j.2 (le_preimage_mono η inf_le_right hL')
    erw [valR_mul_unit η h, valR_mul_unit η h, valR_inv_unit η h,
      valR_res_unit η _ h, valR_res_unit η _ h, valR_res_unit η _ h, valR_res_unit η _ h,
      key _ _ _ (le_preimage_mono η inf_le_left h), key _ _ _ (le_preimage_mono η inf_le_right h)]
    erw [hg, hgM]
    have hzi : z (i.1 PUnit.unit) ≠ 0 := by
      have hh := le_preimage_comp η φ (LB.wchart_le (O1 o M) (fun _ => φ) i.1 PUnit.unit)
        (le_preimage_mono η inf_le_left hM)
      rw [hφ] at hh
      exact (le_point_preimage_iff _).mp hh
    rw [div_pow, inv_div]
    field_simp
  · exact fun k j h => key k j _ h (hsub k j)

end GlobalTheory.TuplePoint
