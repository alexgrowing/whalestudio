import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjBaseChange

open MvPolynomial

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem appLE_cst (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V h).hom.comp (cst f U) = cst (φ ≫ f) V := by
  have e : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ φ.appLE U V h =
      φ.appTop ≫ X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  ext a
  exact congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) e

theorem cst_comp (f' : X' ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (V : X'.Opens) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) V = (cst f' V).comp g := by
  ext a
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact congrArg (fun q => rs X' (le_top : V ≤ ⊤) (f'.appTop.hom q)) e.symm

theorem gs_appLE (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (z : X') (hz : z ∈ V) (a : Γ(X, U)) :
    gs (𝟙 X') z V ((φ.appLE U V h).hom a) = gs φ z U a :=
  (gs_res (𝟙 X') z h hz ((φ.app U).hom a)).trans ((gs_pull (𝟙 X') φ z U (h hz) a).trans (by rw [Category.id_comp]))

theorem isClosedImmersion_of_charts (φ : X' ⟶ X) {J : Type} (U : J → X.Opens) (hc : ⨆ i, U i = ⊤)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (φ ⁻¹ᵁ U i))
    (hs : ∀ i, Function.Surjective (φ.app (U i)).hom) : IsClosedImmersion φ := by
  refine @HasAffineProperty.of_iSup_eq_top _ _ IsClosedImmersion.hasAffineProperty _ _ _ _
    (fun i => ⟨U i, hU i⟩) hc fun i => ⟨hV i, ?_⟩
  have key : ∀ (A : X.Opens) (B : X'.Opens) (h : B ≤ φ ⁻¹ᵁ A), A = U i → B = φ ⁻¹ᵁ U i →
      Function.Surjective (φ.appLE A B h).hom := by
    rintro _ _ h rfl rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact hs i
  show Function.Surjective ((φ ∣_ U i).app ⊤).hom
  rw [morphismRestrict_app']
  exact key _ _ _ (by simp) (by simp)

theorem isPullback_of_charts (g : R →+* R') (hg : Function.Surjective g) (φ : X' ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (hw : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) {J : Type} (U : J → X.Opens) (V : J → X'.Opens)
    (hUV : ∀ i, V i = φ ⁻¹ᵁ U i) (hc : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hs : ∀ i, Function.Surjective (φ.appLE (U i) (V i) (hUV i).le).hom)
    (hk : ∀ i a, (φ.appLE (U i) (V i) (hUV i).le).hom a = 0 → ∀ (B : Type) [CommRing B] (θ : Γ(X, U i) →+* B)
      (c : R' →+* B), θ.comp (cst f (U i)) = c.comp g → θ a = 0) :
    IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  obtain rfl : V = fun i => φ ⁻¹ᵁ U i := funext hUV
  simp only [Scheme.Hom.appLE_eq_app] at hs hk
  have := isClosedImmersion_of_charts φ U hc hU hV hs
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have hle : φ.ker ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom g))).ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i => ⟨U i, hU i⟩) hc fun i a ha => ?_
    rw [Scheme.Hom.ker_apply] at ha ⊢
    refine hk i a ha _ _ (cst (pullback.snd f (Spec.map (CommRingCat.ofHom g))) _) ?_
    rw [← cst_comp, ← pullback.condition, ← appLE_cst _ f le_rfl, Scheme.Hom.appLE_eq_app]
  have hl := IsClosedImmersion.lift_fac φ _ hle
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.fst t.snd t.condition ≫ IsClosedImmersion.lift φ _ hle) (fun t => ?_) (fun t => ?_)
    (fun t m h₁ _ => ?_)⟩⟩
  · rw [Category.assoc, hl, pullback.lift_fst]
  · rw [← cancel_mono (Spec.map (CommRingCat.ofHom g)), Category.assoc, ← hw, ← Category.assoc, Category.assoc _ _ φ,
      hl, pullback.lift_fst, t.condition]
  · rw [← cancel_mono φ, Category.assoc, hl, pullback.lift_fst, h₁]

theorem eventually_exists_form (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {m : ℕ} {s : Fin (m + 1) → H.Sec}
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i)) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (hp : eval₂Hom (cst f _) (r i) p = 0) :
    ∀ᶠ d in Filter.atTop, ∃ F ∈ vanishingForms f s d, MvPolynomial.X i - 1 ∣ F - p := by
  obtain ⟨e, F, hF, hFp⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    obtain ⟨G, hG⟩ := hFp
    rw [eq_add_of_sub_eq hG, map_add, hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup n + e)] with d hd
  obtain ⟨c, rfl⟩ : ∃ c, d = c + e := ⟨d - e, by omega⟩
  refine ⟨MvPolynomial.X i ^ c * F, ?_, ?_⟩
  · refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i c).mul hF) fun j => ?_
    have hle : n j ≤ c := (Finset.le_sup (Finset.mem_univ j)).trans (by omega)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]
  · have : MvPolynomial.X i ^ c * F - p = (MvPolynomial.X i ^ c - 1) * F + (F - p) := by ring
    rw [this]
    exact ((sub_one_dvd_pow_sub_one _ c).mul_right _).add hFp

theorem isPullback_of_equations_lift : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Function.Surjective g → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g)) → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ t₀ : ℕ, (∀ t, t₀ ≤ t → ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f' ≫ (Spec.map (CommRingCat.ofHom g))) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ F₁ : MvPolynomial (Fin (n + 1)) R, F₁.IsHomogeneous t ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F₁) = 0) ∧ MvPolynomial.map g F₁ = MvPolynomial.map g F) → IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  intro R _ X f H n s hH ⟨hc, hs⟩ R' _ g hg X' f' H' s' φ w hH' ⟨hc', hs'⟩ hw _ hrel t₀ hlift
  choose ha r hr hsur using hs
  choose ha' r' hr' hsur' using hs'
  have hR : ∀ i, IsRatioFamily s i (r i) := hr
  have hR' : ∀ i, IsRatioFamily s' i (r' i) := hr'
  have unit : ∀ i z k, φ z ∈ H.U k → (φ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs φ z _ ((s i).f k))) := fun i z k hk =>
    ((mem_nonzeroLocus_iff_isUnit _ hk).trans (LBGerm.isUnit_gs_iff (𝟙 X) _ _ hk _)).trans
      (LBGerm.isUnit_gs_iff φ z _ hk _).symm
  have hUV : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext z
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    refine (mem_nonzeroLocus_iff_isUnit _ hk').trans (Iff.trans ?_ (unit i z k hk).symm)
    rw [hrel i z k k' hk hk', Units.isUnit_units_mul]
  have hrr : ∀ i j, (φ.appLE _ _ (hUV i).le).hom (r i j) = r' i j := fun i j => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    have hz₁ : φ z ∈ nonzeroLocus (s i) := (hUV i).le hz
    have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hz₁, hk⟩
    have e := congrArg (gs φ z _) (hr i j k)
    rw [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e
    rw [gs_appLE φ _ z hz]
    refine ((unit i z k hk).1 hz₁).mul_right_cancel (e.symm.trans ?_)
    rw [hrel j z k k' hk hk', hrel i z k k' hk hk', (hR' i).gs_eq hz hk' j]
    ring
  have hev : ∀ i p, (φ.appLE _ _ (hUV i).le).hom (eval₂Hom (cst f _) (r i) p) =
      eval₂Hom (cst (f' ≫ Spec.map (CommRingCat.ofHom g)) _) (r' i) p := fun i p => by
    rw [map_eval₂Hom, appLE_cst, hw]
    simp only [hrr]
  refine isPullback_of_charts g hg φ f f' hw _ _ hUV hc ha ha' (fun i b => ?_) fun i a h0 B _ θ c hθ => ?_
  · obtain ⟨q, rfl⟩ := hsur' i b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective g hg q
    exact ⟨_, (hev i p).trans (by rw [cst_comp, eval₂Hom_map_hom])⟩
  · obtain ⟨p, rfl⟩ := hsur i a
    rw [hev] at h0
    obtain ⟨t, ht, F, hF, G, hG⟩ := ((Filter.eventually_ge_atTop t₀).and
      (eventually_exists_form _ hc' ha' r' hR' i p h0)).exists
    obtain ⟨F₁, h₁, h₂, h₃⟩ := hlift t ht F hF.1 hF.2
    have e₁ : eval₂Hom (cst f _) (r i) F₁ = 0 := (hR i).eval_eq_zero f ⟨h₁, h₂⟩
    have e₂ : eval₂Hom (cst f _) (r i) p = eval₂Hom (cst f _) (r i) F := by
      rw [eq_add_of_sub_eq hG, map_add, map_mul, map_sub, map_one, eval₂Hom_X', (hR i).self_eq_one]
      simp
    have e₃ : ∀ P, θ (eval₂Hom (cst f _) (r i) P) = eval₂Hom c (fun j => θ (r i j)) (MvPolynomial.map g P) :=
      fun P => by rw [map_eval₂Hom, hθ, eval₂Hom_map_hom]
    rw [e₂, e₃, ← h₃, ← e₃, e₁, map_zero]

end GlobalTheory.ProjBaseChange
