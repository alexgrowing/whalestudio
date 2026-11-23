import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.SegreCoord
open GlobalTheory.ZM.RepBC GlobalTheory.AbLaw.Segre

section Box
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem le_fst {Z : Scheme.{0}} (x : Z ⟶ P) (J : PUnit → (box p q H K).ι) :
    ((box p q H K).pull x).U J ≤ (H.pull (x ≫ p)).U (fun _ => (J PUnit.unit).1) :=
  fun _ h => le_pull H (x ≫ p) (fun _ => (J PUnit.unit).1) (pull_le (box p q H K) x J h).1

theorem le_snd {Z : Scheme.{0}} (x : Z ⟶ P) (J : PUnit → (box p q H K).ι) :
    ((box p q H K).pull x).U J ≤ (K.pull (x ≫ q)).U (fun _ => (J PUnit.unit).2) :=
  fun _ h => le_pull K (x ≫ q) (fun _ => (J PUnit.unit).2) (pull_le (box p q H K) x J h).2

theorem appLE_ap {Z : Scheme.{0}} (x : Z ⟶ P) {U : X.Opens} {V : Y.Opens} {W : P.Opens} {W' : Z.Opens}
    (h₁ : W ≤ p ⁻¹ᵁ U) (h₂ : W ≤ q ⁻¹ᵁ V) (e : W' ≤ x ⁻¹ᵁ W) (e₁ : W' ≤ (x ≫ p) ⁻¹ᵁ U) (e₂ : W' ≤ (x ≫ q) ⁻¹ᵁ V)
    (a : Γ(X, U)) (b : Γ(Y, V)) :
    (x.appLE W W' e).hom (ap p h₁ a * ap q h₂ b) =
      ((x ≫ p).appLE U W' e₁).hom a * ((x ≫ q).appLE V W' e₂).hom b := by
  rw [map_mul]
  exact congrArg₂ (· * ·) (appLE_appLE x p h₁ e e₁ a) (appLE_appLE x q h₂ e e₂ b)

theorem secCoord_box {σ₁ σ₂ : Type} (s : σ₁ → H.Sec) (t : σ₂ → K.Sec) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (v₁ : σ₁ → T) (v₂ : σ₂ → T) (h₁ : SecCoord H s (x ≫ p) v₁) (h₂ : SecCoord K t (x ≫ q) v₂) :
    SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x (fun i => v₁ i.1 * v₂ i.2) := by
  obtain ⟨τ₁, g₁, c₁⟩ := h₁
  obtain ⟨τ₂, g₂, c₂⟩ := h₂
  refine ⟨⟨fun J => res (le_fst p q x J) (τ₁.s _) * res (le_snd p q x J) (τ₂.s _)⟩,
    (isGen_val _).2 fun J J' => ?_, fun i J e => ?_⟩
  · have e₁ := inf_le_inf (le_fst p q x J) (le_fst p q x J')
    have e₂ := inf_le_inf (le_snd p q x J) (le_snd p q x J')
    have a₁ := congrArg (resG (Sp T) e₁) ((isGen_val τ₁).1 g₁ _ _)
    have a₂ := congrArg (resG (Sp T) e₂) ((isGen_val τ₂).1 g₂ _ _)
    rw [map_mul, rr, rr, pull_g _ _ _ _ (pull_inf_le _ _ _ _), r_appLE] at a₁ a₂
    erw [pull_g (box p q H K) x J J' (pull_inf_le _ _ _ _)]
    have l : ∀ (J : PUnit → (box p q H K).ι) (W : (Sp T).Opens) (h : W ≤ ((box p q H K).pull x).U J),
        resG (Sp T) h (res (le_fst p q x J) (τ₁.s _) * res (le_snd p q x J) (τ₂.s _)).val =
        resG (Sp T) (h.trans (le_fst p q x J)) (τ₁.s _).val * resG (Sp T) (h.trans (le_snd p q x J)) (τ₂.s _).val := by
      intro J W h
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (rr _ _ _) (rr _ _ _)
    refine (l J _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (appLE_ap p q x _ _ _
      (e₁.trans (pull_inf_le _ _ _ _)) (e₂.trans (pull_inf_le _ _ _ _)) _ _) (l J' _ _)).symm)
    exact (congrArg₂ (· * ·) a₁ a₂).trans (mul_mul_mul_comm _ _ _ _)
  · have a₁ := congrArg (resG (Sp T) (le_fst p q x J)) (c₁ i.1 _ (pull_le _ _ _))
    have a₂ := congrArg (resG (Sp T) (le_snd p q x J)) (c₂ i.2 _ (pull_le _ _ _))
    rw [map_mul, rr, r_appLE] at a₁ a₂
    refine (appLE_ap p q x _ _ e ((le_fst p q x J).trans (pull_le _ _ _))
      ((le_snd p q x J).trans (pull_le _ _ _)) _ _).trans ?_
    refine (congrArg₂ (· * ·) a₁ a₂).trans ((mul_mul_mul_comm _ _ _ _).trans ?_)
    rw [map_mul, map_mul]
    rfl
end Box

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (spMap_comp f g).symm

section General
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec}

theorem bc (hM : M.IsLB) {T T' : Type} [CommRing T] [CommRing T'] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) (φ : T →+* T') : SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) :=
  (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X M σ th T x v hM h).1 T' φ

theorem scale (hM : M.IsLB) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) (u : Tˣ) : SecCoord M th x (fun i => u * v i) :=
  (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X M σ th T x v hM h).2.1 u

theorem uniq (hM : M.IsLB) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v v' : σ → T}
    (h : SecCoord M th x v) (h' : SecCoord M th x v') : ∃ u : Tˣ, ∀ i, v' i = u * v i :=
  (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X M σ th T x v hM h).2.2 v' h'

theorem eval_smul {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} (hI : ProjRep I s M th)
    {T : Type} [CommRing T] (β : R →+* T) {x : Sp T ⟶ X} {v : σ → T} (hx : x ≫ s = spMap β)
    (h : SecCoord M th x v) (c : T) {F : MvPolynomial σ R} (hF : F ∈ I) :
    MvPolynomial.eval₂ β (fun i => c * v i) F = 0 := by
  let φ : T →+* LaurentPolynomial T := (Polynomial.toLaurent (R := T)).comp Polynomial.C
  have h1 := scale hI.1 (bc hI.1 h φ) (LaurentPolynomial.isUnit_T (R := T) 1).unit
  have h2 := (hI.2.1 _ (φ.comp β) _ _ (by rw [Category.assoc, hx, spc]) h1).2 F hF
  have h3 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply Polynomial.toLaurent_injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h2]
    congr 1
    funext i
    simp [φ]
  have h4 := congrArg (Polynomial.evalRingHom c) h3
  rw [map_zero, MvPolynomial.eval₂_comp_left] at h4
  rw [← h4]
  congr 1
  · ext r; simp
  · funext i; simp; ring

theorem hom_ext_affine {W Z : Scheme.{0}} {T₁ T₂ : Type} [CommRing T₁] [CommRing T₂]
    (a : W ⟶ Sp T₁) (b : W ⟶ Sp T₂) (f : Sp T₁ ⟶ Z) (g : Sp T₂ ⟶ Z)
    (h : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ W) (φ₁ : T₁ →+* T) (φ₂ : T₂ →+* T), y ≫ a = spMap φ₁ →
      y ≫ b = spMap φ₂ → spMap φ₁ ≫ f = spMap φ₂ ≫ g) : a ≫ f = b ≫ g := by
  refine W.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  let y : Sp (W.affineOpenCover.X i) ⟶ W := W.affineOpenCover.f i
  have := h _ y (Spec.preimage (y ≫ a)).hom (Spec.preimage (y ≫ b)).hom (Spec.map_preimage _).symm
    (Spec.map_preimage _).symm
  change y ≫ a ≫ f = y ≫ b ≫ g
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_preimage (y ≫ a), ← Spec.map_preimage (y ≫ b)]
  exact this

theorem glue_points (hM : M.IsLB) {R : Type} [CommRing R] (s : X ⟶ Sp R) {T : Type} [CommRing T] (β : R →+* T)
    (w : σ → T) (hw : Ideal.span (Set.range w) = ⊤)
    (h : ∀ (T' : Type) [CommRing T'] (φ : T →+* T') (k : σ), IsUnit (φ (w k)) →
      ∃! x : Sp T' ⟶ X, x ≫ s = spMap (φ.comp β) ∧ SecCoord M th x (fun i => φ (w i))) :
    ∃! x : Sp T ⟶ X, x ≫ s = spMap β ∧ SecCoord M th x w := by
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of T) w hw).openCover
  have hu : ∀ k, IsUnit (algebraMap T (Localization.Away (w k)) (w k)) := fun k =>
    IsLocalization.Away.algebraMap_isUnit (w k)
  choose x hx hx' using fun k => h (Localization.Away (w k)) (algebraMap _ _) k (hu k)
  have hc : ∀ k l : 𝒰.I₀, pullback.fst (𝒰.f k) (𝒰.f l) ≫ x k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ x l := by
    intro k l
    refine hom_ext_affine _ _ _ _ fun T' _ y φ₁ φ₂ e₁ e₂ => ?_
    have e : φ₁.comp (algebraMap T _) = φ₂.comp (algebraMap T _) := by
      have : spMap (φ₁.comp (algebraMap T _)) = spMap (φ₂.comp (algebraMap T _)) := by
        rw [← spc _ φ₁, ← spc _ φ₂, ← e₁, ← e₂]
        exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) (pullback.condition (f := 𝒰.f k) (g := 𝒰.f l))).trans
          (Category.assoc _ _ _).symm)
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    refine (h T' (φ₁.comp (algebraMap T _)) k ((hu k).map φ₁)).unique ⟨?_, bc hM (hx k).2 φ₁⟩ ⟨?_, ?_⟩
    · rw [Category.assoc, (hx k).1, spc, RingHom.comp_assoc]
    · rw [Category.assoc, (hx l).1, spc, e, RingHom.comp_assoc]
    · rw [e]; exact bc hM (hx l).2 φ₂
  obtain ⟨g, hg⟩ : ∃ g : Sp T ⟶ X, ∀ k, spMap (algebraMap T (Localization.Away (w k))) ≫ g = x k :=
    ⟨𝒰.glueMorphisms x hc, fun k => 𝒰.ι_glueMorphisms x hc k⟩
  refine ⟨g, ⟨𝒰.hom_ext _ _ fun (k : σ) => ?_, ?_⟩, fun y hy => 𝒰.hom_ext _ _ fun (k : σ) => ?_⟩
  · change spMap (algebraMap T (Localization.Away (w k))) ≫ _ = spMap (algebraMap T (Localization.Away (w k))) ≫ _
    rw [← Category.assoc, hg, (hx k).1, spc]
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring X M σ th T _ w hM hw fun p => ?_
    obtain ⟨k, hk⟩ : ∃ k : σ, p ∈ Set.range (spMap (algebraMap T (Localization.Away (w k)))) := 𝒰.exists_eq p
    refine ⟨Localization.Away (w k), inferInstance, algebraMap _ _, inferInstance, hk, ?_⟩
    rw [hg]
    exact (hx k).2
  · change spMap (algebraMap T (Localization.Away (w k))) ≫ _ = spMap (algebraMap T (Localization.Away (w k))) ≫ _
    rw [hg]
    refine hx' k _ ⟨?_, bc hM hy.2 _⟩
    rw [Category.assoc, hy.1, spc]
end General

section Main
variable {X Y P : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y} {σ₁ σ₂ : Type}
  (s : σ₁ → H.Sec) (t : σ₂ → K.Sec)

theorem split_local (hH : H.IsLB) (hK : K.IsLB) {T : Type} [CommRing T] [IsLocalRing T] (x : Sp T ⟶ P)
    (w : σ₁ × σ₂ → T) (hw : SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x w) :
    ∃ a b, SecCoord H s (x ≫ p) a ∧ SecCoord K t (x ≫ q) b ∧ w = fun i => a i.1 * b i.2 := by
  obtain ⟨a, ha⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally X H σ₁ s hH).1 T (x ≫ p)
  obtain ⟨b, hb⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y K σ₂ t hK).1 T (x ≫ q)
  obtain ⟨u, hu⟩ := uniq (isLB_box p q hH hK) (secCoord_box p q s t x a b ha hb) hw
  exact ⟨fun i => u * a i, b, scale hH ha u, hb, funext fun i => (hu i).trans (_root_.mul_assoc _ _ _).symm⟩

theorem split_near (hH : H.IsLB) (hK : K.IsLB) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (w : σ₁ × σ₂ → T) (hw : SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x w)
    (z : Sp T) : ∃ (T' : Type) (_ : CommRing T') (φ : T →+* T'), IsOpenImmersion (spMap φ) ∧
      z ∈ Set.range (spMap φ) ∧ ∃ a b, SecCoord H s (spMap φ ≫ x ≫ p) a ∧ SecCoord K t (spMap φ ≫ x ≫ q) b ∧
        ∀ i, φ (w i) = a i.1 * b i.2 := by
  obtain ⟨f, hf, a, ha⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally X H σ₁ s hH).2.1 T (x ≫ p) z
  obtain ⟨z', hz'⟩ : z ∈ Set.range (spMap (algebraMap T (Localization.Away f))) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge hf
  obtain ⟨g, hg, b, hb⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y K σ₂ t hK).2.1 _
    (spMap (algebraMap T (Localization.Away f)) ≫ x ≫ q) z'
  obtain ⟨z'', hz''⟩ : z' ∈ Set.range (spMap (algebraMap _ (Localization.Away g))) :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge hg
  have ha' := bc hH ha (algebraMap _ (Localization.Away g))
  rw [← Category.assoc, spc] at ha' hb
  set φ := (algebraMap _ (Localization.Away g)).comp (algebraMap T (Localization.Away f)) with hφ
  obtain ⟨u, hu⟩ := uniq (isLB_box p q hH hK)
    (secCoord_box p q s t (spMap φ ≫ x) _ b (by rw [Category.assoc]; exact ha') (by rw [Category.assoc]; exact hb))
    (bc (isLB_box p q hH hK) hw φ)
  refine ⟨_, inferInstance, φ, ?_, ⟨z'', ?_⟩, _, b, scale hH ha' u, hb,
    fun i => (hu i).trans (_root_.mul_assoc _ _ _).symm⟩
  · rw [hφ, ← spc]; infer_instance
  · rw [hφ, ← spc, Scheme.Hom.comp_apply, hz'', hz']

theorem col_row (hH : H.IsLB) (hK : K.IsLB) {T : Type} [CommRing T] (x : Sp T ⟶ P)
    (w : σ₁ × σ₂ → T) (hw : SecCoord (box p q H K) (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) x w)
    (k : σ₁ × σ₂) (hk : IsUnit (w k)) :
    SecCoord H s (x ≫ p) (fun i => w (i, k.2)) ∧ SecCoord K t (x ≫ q) (fun j => w (k.1, j)) := by
  constructor
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring X H σ₁ s T _ _ hH (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k.1, rfl⟩) hk) fun z => ?_
    obtain ⟨T', _, φ, h1, h2, a, b, ha, hb, e⟩ := split_near p q s t hH hK x w hw z
    refine ⟨T', _, φ, h1, h2, ?_⟩
    have hu : IsUnit (b k.2) := isUnit_of_mul_isUnit_right (e k ▸ hk.map φ)
    convert scale hH ha hu.unit using 2 with i
    rw [e, IsUnit.unit_spec, _root_.mul_comm]
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Y K σ₂ t T _ _ hK (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k.2, rfl⟩) hk) fun z => ?_
    obtain ⟨T', _, φ, h1, h2, a, b, ha, hb, e⟩ := split_near p q s t hH hK x w hw z
    refine ⟨T', _, φ, h1, h2, ?_⟩
    have hu : IsUnit (a k.1) := isUnit_of_mul_isUnit_left (e k ▸ hk.map φ)
    convert scale hK hb hu.unit using 2 with i
    rw [e, IsUnit.unit_spec]

theorem mem_graphIdeal {R : Type} [CommRing R] (f : P ⟶ Sp R) (F : MvPolynomial (σ₁ × σ₂) R) :
    F ∈ graphIdeal f H s p K t q ↔ ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ P) (a : σ₁ → T) (b : σ₂ → T),
      y ≫ f = spMap β → SecCoord H s (y ≫ p) a → SecCoord K t (y ≫ q) b →
        MvPolynomial.eval₂ β (fun i : σ₁ × σ₂ => a i.1 * b i.2) F = 0 := by
  simp only [graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, and_imp]

theorem projRep_box {R : Type} [CommRing R] {f : X ⟶ Sp R} {g : Y ⟶ Sp R} (sq : IsPullback p q f g)
    {I₁ : Ideal (MvPolynomial σ₁ R)} {I₂ : Ideal (MvPolynomial σ₂ R)} (h₁ : ProjRep I₁ f H s) (h₂ : ProjRep I₂ g K t) :
    ProjRep (graphIdeal (p ≫ f) H s p K t q) (p ≫ f) (box p q H K)
      (fun i : σ₁ × σ₂ => boxSec p q (s i.1) (t i.2)) := by
  have hB := isLB_box p q h₁.1 h₂.1
  refine ⟨hB, fun T _ β x w hx hw => ⟨?_, fun F hF => ?_⟩, fun T _ β w hw hI => ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field m
    obtain ⟨a, b, ha, hb, e⟩ := split_local p q s t h₁.1 h₂.1 _ _ (bc hB hw (Ideal.Quotient.mk m))
    have ua := (h₁.2.1 _ ((Ideal.Quotient.mk m).comp β) _ a
      (by rw [Category.assoc, Category.assoc, hx, spc]) ha).1
    have ub := (h₂.2.1 _ ((Ideal.Quotient.mk m).comp β) _ b
      (by rw [Category.assoc, Category.assoc, ← sq.w, hx, spc]) hb).1
    have na : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact bot_ne_top ((Ideal.span_eq_bot.2 (by rintro _ ⟨i, rfl⟩; exact h i)).symm.trans ua)
    have nb : ∃ i, b i ≠ 0 := by
      by_contra! h
      exact bot_ne_top ((Ideal.span_eq_bot.2 (by rintro _ ⟨i, rfl⟩; exact h i)).symm.trans ub)
    obtain ⟨i, hi⟩ := na
    obtain ⟨j, hj⟩ := nb
    refine mul_ne_zero hi hj ((congrFun e (i, j)).symm.trans ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨_, rfl⟩))
  · refine eq_zero_of_localization _ fun m hm => ?_
    obtain ⟨a, b, ha, hb, e⟩ := split_local p q s t h₁.1 h₂.1 _ _ (bc hB hw (algebraMap T (Localization.AtPrime m)))
    rw [MvPolynomial.eval₂_comp_left]
    have := (mem_graphIdeal p q s t _ F).1 hF _ ((algebraMap T (Localization.AtPrime m)).comp β) _ a b
      (by rw [Category.assoc, hx, spc]) ha hb
    rw [← e] at this
    exact this
  · refine glue_points hB _ β w hw fun T' _ φ k hk => ?_
    have hI' : ∀ F ∈ graphIdeal (p ≫ f) H s p K t q, MvPolynomial.eval₂ (φ.comp β) (fun i => φ (w i)) F = 0 := by
      intro F hF
      have := congrArg φ (hI F hF)
      rwa [MvPolynomial.eval₂_comp_left, map_zero] at this
    generalize φ.comp β = β' at hI'
    obtain ⟨v, hv⟩ : ∃ v : σ₁ × σ₂ → T', v = fun i => φ (w i) := ⟨_, rfl⟩
    replace hk : IsUnit (v k) := hv ▸ hk
    rw [← hv] at hI' ⊢
    have minor : ∀ i, v (i.1, k.2) * v (k.1, i.2) = v k * v i := by
      intro i
      have := hI' (MvPolynomial.X (i.1, k.2) * MvPolynomial.X (k.1, i.2) - MvPolynomial.X k * MvPolynomial.X i)
        ((mem_graphIdeal p q s t _ _).2 fun T _ β y a b _ _ _ => by simp; ring)
      simpa [sub_eq_zero] using this
    obtain ⟨y₁, ⟨e₁, c₁⟩, u₁⟩ := h₁.2.2 T' β' (fun i => v (i, k.2))
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k.1, rfl⟩) hk) fun F hF => by
        have := hI' (MvPolynomial.rename (fun i => (i, k.2)) F)
          ((mem_graphIdeal p q s t _ _).2 fun T _ β y a b hy ha _ => by
            rw [MvPolynomial.eval₂_rename, ← eval_smul h₁ β (by rw [Category.assoc, hy]) ha (b k.2) hF]
            congr 1; funext i; exact _root_.mul_comm _ _)
        rwa [MvPolynomial.eval₂_rename] at this
    obtain ⟨y₂, ⟨e₂, c₂⟩, u₂⟩ := h₂.2.2 T' β' (fun j => v (k.1, j))
      (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k.2, rfl⟩) hk) fun F hF => by
        have := hI' (MvPolynomial.rename (fun j => (k.1, j)) F)
          ((mem_graphIdeal p q s t _ _).2 fun T _ β y a b hy _ hb => by
            rw [MvPolynomial.eval₂_rename]
            exact eval_smul h₂ β (by rw [Category.assoc, ← sq.w, hy]) hb (a k.1) hF)
        rwa [MvPolynomial.eval₂_rename] at this
    refine ⟨sq.lift y₁ y₂ (e₁.trans e₂.symm), ⟨by rw [sq.lift_fst_assoc, e₁], ?_⟩, fun y hy => ?_⟩
    · have := scale hB (secCoord_box p q s t (sq.lift y₁ y₂ (e₁.trans e₂.symm)) _ _
        (by rw [sq.lift_fst]; exact c₁) (by rw [sq.lift_snd]; exact c₂)) hk.unit⁻¹
      convert this using 2 with i
      rw [minor, ← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul]
    · obtain ⟨d₁, d₂⟩ := col_row p q s t h₁.1 h₂.1 y v hy.2 k hk
      apply sq.hom_ext
      · rw [sq.lift_fst]
        exact u₁ _ ⟨by rw [Category.assoc, hy.1], d₁⟩
      · rw [sq.lift_snd]
        exact u₂ _ ⟨by rw [Category.assoc, ← sq.w, hy.1], d₂⟩
end Main

theorem segre_coordinates : ∀ (R σ₁ σ₂ : Type) [CommRing R] [Finite σ₁] [Finite σ₂] (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → ∃ (I₃ : Ideal (MvPolynomial (σ₁ × σ₂) R)) (M₃ : LB (Z₁ ⊗ Z₂).left) (th₃ : σ₁ × σ₂ → M₃.Sec), ProjRep I₃ (Z₁ ⊗ Z₂).hom M₃ th₃ ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ (Z₁ ⊗ Z₂).left) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (x ≫ (fst Z₁ Z₂).left) v₁ → SecCoord M₂ th₂ (x ≫ (snd Z₁ Z₂).left) v₂ → SecCoord M₃ th₃ x (fun i => v₁ i.1 * v₂ i.2) := by
  intro R σ₁ σ₂ _ _ _ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ h₁ h₂
  exact ⟨_, _, _, projRep_box _ _ th₁ th₂ (IsPullback.of_hasPullback Z₁.hom Z₂.hom) h₁ h₂,
    fun T _ x v₁ v₂ => secCoord_box _ _ th₁ th₂ x v₁ v₂⟩

end GlobalTheory.ZM.SegreCoord
end
