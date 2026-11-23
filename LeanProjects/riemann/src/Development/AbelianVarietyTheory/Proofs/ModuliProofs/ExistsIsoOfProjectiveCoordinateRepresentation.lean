import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace

variable {σ : Type} {T T' X X' X'' : Scheme.{0}}

def NoZero {W : T.Opens} (f : σ → Γ(T, W)) : Prop :=
  ∀ t (ht : t ∈ W), ∃ i, IsUnit ((T.presheaf.germ W t ht).hom (f i))

theorem NoZero.res {W W' : T.Opens} {f : σ → Γ(T, W)} (hf : NoZero f) (h : W' ≤ W) :
    NoZero fun i => resG T h (f i) := fun t ht =>
  (hf t (h ht)).imp fun i hi => by rwa [germ_resG]

theorem NoZero.cancel {W : T.Opens} {f : σ → Γ(T, W)} (hf : NoZero f) {a b : Γ(T, W)}
    (h : ∀ i, a * f i = b * f i) : a = b :=
  ext_germ fun t ht => by
    obtain ⟨i, hi⟩ := hf t ht
    have := congrArg (T.presheaf.germ W t ht).hom (h i)
    rw [map_mul, map_mul] at this
    exact hi.mul_right_cancel this

theorem NoZero.glue {W : T.Opens} {f f' : σ → Γ(T, W)} (hf : NoZero f)
    (H : ∀ t ∈ W, ∃ (V : T.Opens) (h : V ≤ W), t ∈ V ∧ ∃ u : Γ(T, V), IsUnit u ∧
      ∀ i, resG T h (f' i) = u * resG T h (f i)) :
    ∃ u : Γ(T, W), IsUnit u ∧ ∀ i, f' i = u * f i := by
  choose V hV ht u hu e using fun t : W => H t.1 t.2
  obtain ⟨r, hr'⟩ : ∃ r : Γ(T, W), ∀ t, resG T (hV t) r = u t :=
    (T.sheaf.existsUnique_gluing' V W (fun t => homOfLE (hV t))
    (fun t h => Opens.mem_iSup.2 ⟨⟨t, h⟩, ht _⟩) u (fun a b => by
      refine (hf.res (inf_le_left.trans (hV a) : V a ⊓ V b ≤ W)).cancel fun i => ?_
      have e₁ := congrArg (resG T (inf_le_left : V a ⊓ V b ≤ _)) (e a i)
      have e₂ := congrArg (resG T (inf_le_right : V a ⊓ V b ≤ _)) (e b i)
      rw [map_mul, resG_resG, resG_resG] at e₁ e₂
      exact e₁.symm.trans e₂)).exists
  refine ⟨r, T.toRingedSpace.isUnit_of_isUnit_germ _ _ fun t h => ?_, fun i => ext_germ fun t h => ?_⟩
  · have := (hu ⟨t, h⟩).map (T.presheaf.germ _ t (ht ⟨t, h⟩)).hom
    rwa [← hr', germ_resG] at this
  · have := congrArg (T.presheaf.germ _ t (ht ⟨t, h⟩)).hom (e ⟨t, h⟩ i)
    rwa [← hr', ← map_mul, germ_resG, germ_resG] at this

theorem appLE_compat {M : LB X} (a : M.Sec) (x : T ⟶ X) {W : T.Opens} (j k : M.ι) (hj : W ≤ x ⁻¹ᵁ M.U j)
    (hk : W ≤ x ⁻¹ᵁ M.U k) :
    (x.appLE _ W hj).hom (a.f j) =
      (x.appLE (M.U j ⊓ M.U k) W (le_inf hj hk)).hom (M.g j k).val * (x.appLE _ W hk).hom (a.f k) := by
  have h : W ≤ x ⁻¹ᵁ (M.U j ⊓ M.U k) := le_inf hj hk
  have := congrArg (x.appLE (M.U j ⊓ M.U k) W h).hom (a.compat j k)
  rw [map_mul] at this
  exact (appLE_resG x inf_le_left h _).symm.trans
    (this.trans (congrArg (_ * ·) (appLE_resG x inf_le_right h _)))

def Frame (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (W : T.Opens) (f : σ → Γ(T, W)) : Prop :=
  ∃ (j : M.ι) (h : W ≤ x ⁻¹ᵁ M.U j) (u : Γ(T, W)), IsUnit u ∧ ∀ i, (x.appLE _ W h).hom ((th i).f j) = u * f i

variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}

theorem frame_chart (j : M.ι) {W : T.Opens} (h : W ≤ x ⁻¹ᵁ M.U j) :
    Frame M th x W fun i => (x.appLE _ W h).hom ((th i).f j) :=
  ⟨j, h, 1, isUnit_one, fun _ => (one_mul _).symm⟩

theorem Frame.res {W W' : T.Opens} {f : σ → Γ(T, W)} (H : Frame M th x W f) (h : W' ≤ W) :
    Frame M th x W' fun i => resG T h (f i) := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  exact ⟨j, h.trans hj, resG T h u, hu.map _, fun i => by rw [← map_mul, ← e, resG_appLE]⟩

theorem Frame.comp {W : T.Opens} {f : σ → Γ(T, W)} (H : Frame M th x W f) (g : T' ⟶ T) {W' : T'.Opens}
    (h : W' ≤ g ⁻¹ᵁ W) : Frame M th (g ≫ x) W' fun i => (g.appLE W W' h).hom (f i) := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  exact ⟨j, h.trans (g.preimage_mono hj), (g.appLE W W' h).hom u, hu.map _,
    fun i => by rw [← map_mul, ← e, appLE_appLE]⟩

theorem Frame.mul {W : T.Opens} {f f' : σ → Γ(T, W)} (H : Frame M th x W f') {c : Γ(T, W)} (hc : IsUnit c)
    (h : ∀ i, f' i = c * f i) : Frame M th x W f := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  exact ⟨j, hj, u * c, hu.mul hc, fun i => by rw [e, h, mul_assoc]⟩

theorem Frame.ratio {W : T.Opens} {f f' : σ → Γ(T, W)} (H : Frame M th x W f) (H' : Frame M th x W f') :
    ∃ c : Γ(T, W), IsUnit c ∧ ∀ i, f' i = c * f i := by
  obtain ⟨j, hj, u, hu, e⟩ := H
  obtain ⟨k, hk, u', hu', e'⟩ := H'
  obtain ⟨u', rfl⟩ := hu'
  refine ⟨u'⁻¹.val * (x.appLE (M.U k ⊓ M.U j) W (le_inf hk hj)).hom (M.g k j).val * u,
    ((Units.isUnit _).mul ((Units.isUnit _).map _)).mul hu, fun i => ?_⟩
  rw [mul_assoc, ← e, mul_assoc, ← appLE_compat _ x k j hk hj, e', Units.inv_mul_cancel_left]

def Same (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (M' : LB X') (th' : σ → M'.Sec) (x' : T ⟶ X') : Prop :=
  ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ ∃ f, Frame M th x W f ∧ Frame M' th' x' W f

theorem Same.symm (H : Same M th x M' th' x') : Same M' th' x' M th x := fun t =>
  (H t).imp fun _ h => ⟨h.1, h.2.imp fun _ h => h.symm⟩

theorem Same.trans (H : Same M th x M' th' x') (H' : Same M' th' x' M'' th'' x'') :
    Same M th x M'' th'' x'' := fun t => by
  obtain ⟨W, hW, f, h₁, h₂⟩ := H t
  obtain ⟨V, hV, f', h₃, h₄⟩ := H' t
  obtain ⟨c, hc, e⟩ := (h₂.res (inf_le_left : W ⊓ V ≤ W)).ratio (h₃.res inf_le_right)
  exact ⟨W ⊓ V, ⟨hW, hV⟩, _, h₁.res inf_le_left, (h₄.res inf_le_right).mul hc e⟩

theorem Same.comp (H : Same M th x M' th' x') (g : T' ⟶ T) : Same M th (g ≫ x) M' th' (g ≫ x') := fun t => by
  obtain ⟨W, hW, f, h₁, h₂⟩ := H (g t)
  exact ⟨g ⁻¹ᵁ W, hW, _, h₁.comp g le_rfl, h₂.comp g le_rfl⟩

def LocCoord (M : LB X) (th : σ → M.Sec) (x : T ⟶ X) (v : σ → Γ(T, ⊤)) : Prop :=
  ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ Frame M th x W fun i => resG T le_top (v i)

theorem LocCoord.same {v : σ → Γ(T, ⊤)} (H : LocCoord M th x v) (H' : LocCoord M' th' x' v) :
    Same M th x M' th' x' := fun t => by
  obtain ⟨W, hW, h₁⟩ := H t
  obtain ⟨V, hV, h₂⟩ := H' t
  have h₃ := h₁.res (inf_le_left : W ⊓ V ≤ W)
  have h₄ := h₂.res (inf_le_right : W ⊓ V ≤ V)
  simp only [resG_resG] at h₃ h₄
  exact ⟨W ⊓ V, ⟨hW, hV⟩, _, h₃, h₄⟩

theorem LocCoord.of_same {v : σ → Γ(T, ⊤)} (H : LocCoord M th x v) (H' : Same M th x M' th' x') :
    LocCoord M' th' x' v := fun t => by
  obtain ⟨W, hW, h₁⟩ := H t
  obtain ⟨V, hV, f', h₃, h₄⟩ := H' t
  obtain ⟨c, hc, e⟩ := (h₁.res (inf_le_left : W ⊓ V ≤ W)).ratio (h₃.res inf_le_right)
  refine ⟨W ⊓ V, ⟨hW, hV⟩, (h₄.res inf_le_right).mul hc fun i => (e i).trans ?_⟩
  rw [resG_resG]

theorem resG_pull_g (x : T ⟶ X) (j k : PUnit → M.ι) {W : T.Opens} (hj : W ≤ (M.pull x).U j)
    (hk : W ≤ (M.pull x).U k) :
    resG T (le_inf hj hk) ((M.pull x).g j k).val =
      (x.appLE (M.U (j ⟨⟩) ⊓ M.U (k ⟨⟩)) W
        (le_inf (hj.trans (pull_U M x j).le) (hk.trans (pull_U M x k).le))).hom (M.g (j ⟨⟩) (k ⟨⟩)).val := by
  refine (congrArg (fun u => resG T (le_inf hj hk) (Units.val u)) (pull_g M x j k)).trans ?_
  exact resG_resG _ _ _

section Ring
variable {A : Type} [CommRing A]

abbrev fn (v : σ → A) : σ → Γ(Sp A, ⊤) := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (v i)

theorem noZero_of_span {W : T.Opens} {f : σ → Γ(T, W)} (h : Ideal.span (Set.range f) = ⊤) : NoZero f := by
  intro t ht
  by_contra hn
  push_neg at hn
  have : Ideal.span (Set.range f) ≤
      (IsLocalRing.maximalIdeal _).comap (T.presheaf.germ W t ht).hom :=
    Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hn i)
  have h1 := this (h.ge (Submodule.mem_top (x := 1)))
  rw [Ideal.mem_comap, map_one] at h1
  exact h1 isUnit_one

theorem span_map_eq_top {B : Type} [CommRing B] (φ : A →+* B) {v : σ → A} (h : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range fun i => φ (v i)) = ⊤ := by
  have := congrArg (Ideal.map φ) h
  rwa [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at this

theorem locCoord_of_secCoord (hM : M.IsLB) {x : Sp A ⟶ X} {v : σ → A} (H : SecCoord M th x v) :
    LocCoord M th x (fn v) := fun t => by
  obtain ⟨τ, -, e⟩ := H
  obtain ⟨j, hj⟩ := LB.mem_of_cover hM (x t)
  exact ⟨(M.pull x).U fun _ => j, (pull_U M x fun _ => j).ge hj, j, (pull_U M x fun _ => j).le,
    (τ.s fun _ => j).val, Units.isUnit _, fun i => (e i (fun _ => j) _).trans (mul_comm _ _)⟩

theorem secCoord_of_locCoord {x : Sp A ⟶ X} {v : σ → A} (hv : Ideal.span (Set.range v) = ⊤)
    (H : LocCoord M th x (fn v)) : SecCoord M th x v := by
  have nz : NoZero (fn v) := noZero_of_span (span_map_eq_top _ hv)
  have key : ∀ j : PUnit → M.ι, ∃ u : Γ(Sp A, (M.pull x).U j), IsUnit u ∧ ∀ i,
      (x.appLE _ _ (pull_U M x j).le).hom ((th i).f (j ⟨⟩)) = u * resG _ le_top (fn v i) := fun j =>
    (nz.res le_top).glue fun t ht => by
      obtain ⟨W, hW, h₁⟩ := H t
      obtain ⟨c, hc, e⟩ := (h₁.res (inf_le_left : W ⊓ (M.pull x).U j ≤ W)).ratio
        ((frame_chart (j ⟨⟩) (pull_U M x j).le).res inf_le_right)
      exact ⟨W ⊓ (M.pull x).U j, inf_le_right, ⟨hW, ht⟩, c, hc, fun i => (e i).trans (by
        rw [resG_resG, resG_resG])⟩
  choose u hu e using key
  refine ⟨⟨fun j => (hu j).unit⟩, fun j k => Units.ext ?_, fun i j _ => (e j i).trans (mul_comm _ _)⟩
  change resG _ inf_le_left (u j) = ((M.pull x).g j k).val * resG _ inf_le_right (u k)
  refine (nz.res (le_top : (M.pull x).U j ⊓ (M.pull x).U k ≤ ⊤)).cancel fun i => ?_
  have e₁ := congrArg (resG _ (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U k ≤ _)) (e j i)
  have e₂ := congrArg (resG _ (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U k ≤ _)) (e k i)
  rw [map_mul, resG_resG, resG_appLE] at e₁ e₂
  have e₃ := resG_pull_g x j k (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U k ≤ _) inf_le_right
  rw [resG_self] at e₃
  rw [← e₁, mul_assoc, ← e₂, e₃]
  exact appLE_compat _ _ _ _ _ _

end Ring

section Top
variable {A : Type} [CommRing A]

theorem secCoord_of_frame (hM : M.IsLB) {x : Sp A ⟶ X} {v : σ → A} (H : Frame M th x ⊤ (fn v)) :
    SecCoord M th x v := by
  obtain ⟨j, hj, u, ⟨u, rfl⟩, e⟩ := H
  have hle : ∀ k : PUnit → M.ι, (M.pull x).U k ≤ x ⁻¹ᵁ (M.U (k ⟨⟩) ⊓ M.U j) := fun k =>
    le_inf (pull_U M x k).le (le_top.trans hj)
  refine ⟨⟨fun k => res (hle k) (pullU x _ (M.g (k ⟨⟩) j)) * res le_top u⟩, fun k l => ?_, fun i k h => ?_⟩
  · change res inf_le_left (res (hle k) (pullU x _ (M.g (k ⟨⟩) j)) * res le_top u) =
      (M.pull x).g k l * res inf_le_right (res (hle l) (pullU x _ (M.g (l ⟨⟩) j)) * res le_top u)
    rw [pull_g M x k l, map_mul, map_mul, LB.res_res, LB.res_res, LB.res_res, LB.res_res]
    exact (congrArg (· * _) (LB.pull_cocycle hM x _ _ _ _ _ _).symm).trans (mul_assoc _ _ _)
  · have e₁ := congrArg (resG _ (le_top : (M.pull x).U k ≤ ⊤)) (e i)
    rw [map_mul, resG_appLE] at e₁
    refine (appLE_compat _ x (k ⟨⟩) j h (le_top.trans hj)).trans ?_
    rw [e₁, ← mul_assoc, mul_comm]
    rfl

end Top

theorem fromSpec_appLE_top {U : T.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)

theorem exists_affine_secCoord (hM : M.IsLB) (th : σ → M.Sec) (x : T ⟶ X) (t : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W) (j : M.ι) (h : W ≤ x ⁻¹ᵁ M.U j), t ∈ W ∧
      SecCoord (R := Γ(T, W)) M th (hW.fromSpec ≫ x) fun i => (x.appLE _ W h).hom ((th i).f j) := by
  obtain ⟨j, hj⟩ := LB.mem_of_cover hM (x t)
  obtain ⟨W, hW, ht, h⟩ := exists_isAffineOpen_mem_and_subset (U := x ⁻¹ᵁ M.U j) (x := t) hj
  refine ⟨W, hW, j, h, ht, secCoord_of_frame hM ?_⟩
  have := (frame_chart (th := th) j h).comp hW.fromSpec hW.fromSpec_preimage_self.ge
  rw [fromSpec_appLE_top] at this
  exact this

theorem same_of_local (H : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ Same M th (W.ι ≫ x) M' th' (W.ι ≫ x')) :
    Same M th x M' th' x' := fun t => by
  obtain ⟨W, ht, h⟩ := H t
  obtain ⟨V, hV, f, ⟨j, hj, u, hu, e⟩, ⟨k, hk, u', hu', e'⟩⟩ := h ⟨t, ht⟩
  have hle : V ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ V) := (W.ι.preimage_image_eq V).ge
  have : IsIso (W.ι.appLE (W.ι ''ᵁ V) V hle) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (W.ι.appLE (W.ι ''ᵁ V) V hle)
  let φ := RingEquiv.ofBijective (W.ι.appLE (W.ι ''ᵁ V) V hle).hom hb
  have h₁ : W.ι ''ᵁ V ≤ x ⁻¹ᵁ M.U j := by
    rintro _ ⟨y, hy, rfl⟩
    exact hj hy
  have h₂ : W.ι ''ᵁ V ≤ x' ⁻¹ᵁ M'.U k := by
    rintro _ ⟨y, hy, rfl⟩
    exact hk hy
  refine ⟨W.ι ''ᵁ V, ⟨⟨t, ht⟩, hV, rfl⟩, fun i => φ.symm (f i),
    ⟨j, h₁, φ.symm u, hu.map _, fun i => φ.injective ?_⟩, ⟨k, h₂, φ.symm u', hu'.map _, fun i => φ.injective ?_⟩⟩
  · rw [← map_mul, φ.apply_symm_apply, ← e]
    exact appLE_appLE _ _ _ _ _
  · rw [← map_mul, φ.apply_symm_apply, ← e']
    exact appLE_appLE _ _ _ _ _

section Rep
variable {R : Type} [CommRing R] {I I' : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R}

theorem exists_spMap {A : Type} [CommRing A] (p : Sp A ⟶ Sp R) : ∃ β : R →+* A, p = spMap β :=
  ⟨(Spec.preimage p).hom, (Spec.map_preimage p).symm⟩

theorem span_eq_top (h : ProjRep I s M th) {A : Type} [CommRing A] {x : Sp A ⟶ X} {v : σ → A}
    (H : SecCoord M th x v) : Ideal.span (Set.range v) = ⊤ :=
  (exists_spMap (x ≫ s)).elim fun β hβ => (h.2.1 A β x v hβ H).1

theorem secCoord_of_same (h : ProjRep I s M th) {A : Type} [CommRing A] {x : Sp A ⟶ X} {x' : Sp A ⟶ X'}
    {v : σ → A} (H : SecCoord M th x v) (H' : Same M th x M' th' x') : SecCoord M' th' x' v :=
  secCoord_of_locCoord (span_eq_top h H) ((locCoord_of_secCoord h.1 H).of_same H')

theorem isoSpec_hom_fromSpec {W : T.Opens} (hW : IsAffineOpen W) : hW.isoSpec.hom ≫ hW.fromSpec = W.ι := by
  rw [← hW.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

theorem eq_of_same (h : ProjRep I s M th) {x y : T ⟶ X} (hs : x ≫ s = y ≫ s) (H : Same M th x M th y) :
    x = y := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, j, hj, ht, hc⟩ := exists_affine_secCoord h.1 th x t
  obtain ⟨β, hβ⟩ := exists_spMap (A := Γ(T, W)) ((hW.fromSpec ≫ x) ≫ s)
  obtain ⟨h₁, h₂⟩ := h.2.1 _ β _ _ hβ hc
  have hy := secCoord_of_same h hc (H.comp hW.fromSpec)
  have e : hW.fromSpec ≫ x = hW.fromSpec ≫ y := (h.2.2 _ β _ h₁ h₂).unique ⟨hβ, hc⟩
    ⟨((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs.symm)).trans ((Category.assoc _ _ _).symm.trans hβ), hy⟩
  refine ⟨W, ht, ?_⟩
  rw [← isoSpec_hom_fromSpec hW, Category.assoc, Category.assoc, e]

theorem exists_hom (h : ProjRep I s M th) (h' : ProjRep I' s' M' th')
    (hI : ∀ (A : Type) [CommRing A] (β : R →+* A) (v : σ → A), Ideal.span (Set.range v) = ⊤ →
      (∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∀ F ∈ I', MvPolynomial.eval₂ β v F = 0) :
    ∃ e : X ⟶ X', e ≫ s' = s ∧ Same M th (𝟙 X) M' th' e := by
  have loc : ∀ t : X, ∃ W : X.Opens, t ∈ W ∧ ∃ m : W.toScheme ⟶ X', m ≫ s' = W.ι ≫ s ∧
      Same M th W.ι M' th' m := fun t => by
    obtain ⟨W, hW, j, hj, ht, hc⟩ := exists_affine_secCoord h.1 th (𝟙 X) t
    rw [Category.comp_id] at hc
    obtain ⟨β, hβ⟩ := exists_spMap (A := Γ(X, W)) (hW.fromSpec ≫ s)
    obtain ⟨h₁, h₂⟩ := h.2.1 _ β _ _ hβ hc
    obtain ⟨y, ⟨hy, hy'⟩, -⟩ := h'.2.2 _ β _ h₁ (hI _ β _ h₁ h₂)
    refine ⟨W, ht, hW.isoSpec.hom ≫ y, ?_, ?_⟩
    · rw [← isoSpec_hom_fromSpec hW, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) (hy.trans hβ.symm)
    · rw [← isoSpec_hom_fromSpec hW]
      exact ((locCoord_of_secCoord h.1 hc).same (locCoord_of_secCoord h'.1 hy')).comp _
  choose W ht m hm hS using loc
  have hcov : IsOpenCover W := eq_top_iff.2 fun t _ => Opens.mem_iSup.2 ⟨t, ht t⟩
  let 𝒰 := X.openCoverOfIsOpenCover W hcov
  have hc : ∀ a b : X, pullback.fst (W a).ι (W b).ι ≫ m a = pullback.snd (W a).ι (W b).ι ≫ m b := fun a b => by
    refine eq_of_same h' ?_ ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · have h₁ := ((hS a).comp (pullback.fst (W a).ι (W b).ι)).symm
      rw [pullback.condition] at h₁
      exact h₁.trans ((hS b).comp _)
  have hg : ∀ t : X, (W t).ι ≫ 𝒰.glueMorphisms m hc = m t := fun t => 𝒰.ι_glueMorphisms m hc t
  refine ⟨𝒰.glueMorphisms m hc, Scheme.hom_ext_of_forall _ _ fun t => ⟨W t, ht t, ?_⟩,
    same_of_local fun t => ⟨W t, ht t, ?_⟩⟩
  · rw [← Category.assoc, hg, hm]
  · rw [hg, Category.comp_id]
    exact hS t

theorem noZero_chart (h : ProjRep I s M th) (k : M.ι) : NoZero fun i => (th i).f k := fun t ht => by
  obtain ⟨W, hW, j, hj, htW, hc⟩ := exists_affine_secCoord h.1 th (𝟙 X) t
  obtain ⟨i, hi⟩ := noZero_of_span (span_eq_top h hc) t htW
  refine ⟨i, ?_⟩
  have hm : t ∈ W ⊓ M.U k := ⟨htW, ht⟩
  have e := congrArg (X.presheaf.germ _ t hm).hom (sec_compat (th i) j k (inf_le_left.trans hj) inf_le_right)
  rw [map_mul, germ_resG, germ_resG, germ_resG] at e
  have hi' : IsUnit ((X.presheaf.germ _ t (hj htW)).hom ((th i).f j)) :=
    (congrArg IsUnit (germ_resG hj t htW ((th i).f j))).mp hi
  exact isUnit_of_mul_isUnit_right ((congrArg IsUnit e).mp hi')

theorem lbIso_of_same (h : ProjRep I s M th) {e : X ⟶ X'} (H : Same M th (𝟙 X) M' th' e) :
    LBIso M (M'.pull e) := by
  let B := M'.pull e
  have key : ∀ p : (PUnit → M'.ι) × M.ι, ∃ u : Γ(X, B.U p.1 ⊓ M.U p.2), IsUnit u ∧ ∀ i,
      (e.appLE _ _ (inf_le_left.trans (pull_U M' e p.1).le)).hom ((th' i).f (p.1 ⟨⟩)) =
        u * resG X inf_le_right ((th i).f p.2) := fun p =>
    ((noZero_chart h p.2).res inf_le_right).glue fun t ht => by
      obtain ⟨W, hW, f, h₁, h₂⟩ := H t
      have hp : B.U p.1 ⊓ M.U p.2 ≤ 𝟙 X ⁻¹ᵁ M.U p.2 := inf_le_right
      obtain ⟨c, hc, e₁⟩ := ((frame_chart (th := th) (x := 𝟙 X) p.2 hp).res inf_le_right).ratio
        (h₁.res (inf_le_left : W ⊓ (B.U p.1 ⊓ M.U p.2) ≤ W))
      obtain ⟨d, hd, e₂⟩ := (h₂.res (inf_le_left : W ⊓ (B.U p.1 ⊓ M.U p.2) ≤ W)).ratio
        ((frame_chart (p.1 ⟨⟩) (inf_le_left.trans (pull_U M' e p.1).le)).res inf_le_right)
      refine ⟨W ⊓ (B.U p.1 ⊓ M.U p.2), inf_le_right, ⟨hW, ht⟩, d * c, hd.mul hc, fun i => (e₂ i).trans ?_⟩
      rw [mul_assoc]
      exact congrArg (d * ·) (e₁ i)
  choose u hu E using key
  refine ⟨⟨fun p => (hu p).unit⟩, ?_⟩
  rintro ⟨p, q⟩ ⟨p', q'⟩
  have hp : B.U p ⊓ M.U q ⊓ (B.U p' ⊓ M.U q') ≤ B.U p := inf_le_left.trans inf_le_left
  have hq : B.U p ⊓ M.U q ⊓ (B.U p' ⊓ M.U q') ≤ M.U q := inf_le_left.trans inf_le_right
  have hp' : B.U p ⊓ M.U q ⊓ (B.U p' ⊓ M.U q') ≤ B.U p' := inf_le_right.trans inf_le_left
  have hq' : B.U p ⊓ M.U q ⊓ (B.U p' ⊓ M.U q') ≤ M.U q' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (hu (p, q)).unit * res (le_inf hq hq') (M.g q q') =
      res (le_inf hp hp') (B.g p p') * res (le_inf hp' hq') (hu (p', q')).unit := by
    refine Units.ext ?_
    change resG X (le_inf hp hq) (u (p, q)) * resG X (le_inf hq hq') (M.g q q').val =
      resG X (le_inf hp hp') (B.g p p').val * resG X (le_inf hp' hq') (u (p', q'))
    refine ((noZero_chart h q').res hq').cancel fun i => ?_
    have e₁ := congrArg (resG X (le_inf hp hq)) (E (p, q) i)
    have e₂ := congrArg (resG X (le_inf hp' hq')) (E (p', q') i)
    rw [map_mul, resG_resG, resG_appLE] at e₁ e₂
    rw [mul_assoc, mul_assoc, ← sec_compat (th i) q q' hq hq', ← e₁, ← e₂, resG_pull_g e p p' hp hp']
    exact appLE_compat _ _ _ _ _ _
  change res (le_inf hp hq) (hu (p, q)).unit =
    res (le_inf hp hp') (B.g p p') * (res (le_inf hq hq') (M.g q q'))⁻¹ * res (le_inf hp' hq') (hu (p', q')).unit
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

end Rep

theorem exists_iso_of_projRep : ∀ (R σ : Type) [CommRing R] (I I' : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R) (M : LB Z) (M' : LB Z') (th : σ → M.Sec) (th' : σ → M'.Sec), ProjRep I s M th → ProjRep I' s' M' th' → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → ((∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ↔ ∀ F ∈ I', MvPolynomial.eval₂ β v F = 0)) → ∃ e : Z ≅ Z', e.hom ≫ s' = s ∧ LBIso M (M'.pull e.hom) ∧ ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Z) (v : σ → R'), SecCoord M th x v ↔ SecCoord M' th' (x ≫ e.hom) v := by
  intro R σ _ I I' Z Z' s s' M M' th th' h h' hI
  obtain ⟨a, ha, Ha⟩ := exists_hom h h' fun A _ β v hv => (hI A β v hv).1
  obtain ⟨b, hb, Hb⟩ := exists_hom h' h fun A _ β v hv => (hI A β v hv).2
  have Hab := Hb.comp a
  have Hba := Ha.comp b
  rw [Category.comp_id] at Hab Hba
  refine ⟨⟨a, b, eq_of_same h ?_ (Ha.trans Hab).symm, eq_of_same h' ?_ (Hb.trans Hba).symm⟩, ha,
    lbIso_of_same h Ha, fun A _ x v => ?_⟩
  · rw [Category.assoc, hb, ha, Category.id_comp]
  · rw [Category.assoc, ha, hb, Category.id_comp]
  · have Hx := Ha.comp x
    rw [Category.comp_id] at Hx
    exact ⟨fun H => secCoord_of_same h H Hx, fun H => secCoord_of_same h' H Hx.symm⟩

end GlobalTheory.RepUniq
