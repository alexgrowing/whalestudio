import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)

theorem eval₂_scale {R A σ : Type} [CommRing R] [CommRing A] (φ : R →+* A) (x : σ → A) (c : A)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}

theorem mem_idealOf {F : MvPolynomial σ R} : F ∈ idealOf p M th (𝟙 X) ↔
    ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ X) (v : σ → T), y ≫ p = spMap β → SecCoord M th y v →
      MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id, and_imp]

theorem homogeneousComponent_mem {F : MvPolynomial σ R} (hF : F ∈ idealOf p M th (𝟙 X)) (e : ℕ) :
    MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  let φ : T →+* LaurentPolynomial T := (Polynomial.toLaurent (R := T)).comp Polynomial.C
  have h1 := Coord.scale (Coord.baseChange h φ) (LaurentPolynomial.isUnit_T (R := T) 1).unit
  have h2 := mem_idealOf.1 hF _ (φ.comp β) _ _ (by rw [Category.assoc, hx]; exact (spMap_comp β φ).symm) h1
  have h3 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply Polynomial.toLaurent_injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h2]
    congr 1
    funext i
    simp [φ]
  have h4 : ∀ n, MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i))
      (MvPolynomial.homogeneousComponent n F) =
      Polynomial.monomial n (MvPolynomial.eval₂ β v (MvPolynomial.homogeneousComponent n F)) := fun n => by
    rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous n F), ← Polynomial.C_mul_X_pow_eq_monomial,
      _root_.mul_comm, MvPolynomial.eval₂_comp_left]
    rfl
  by_cases he : F.totalDegree < e
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ he, MvPolynomial.eval₂_zero]
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum] at h3
  have h5 := congrArg (fun q => Polynomial.coeff q e) h3
  simp only [h4, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range,
    Polynomial.coeff_zero] at h5
  rwa [if_pos (by omega)] at h5

theorem isUnit_gs_iff {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff, X.mem_basicOpen a _ h]

theorem not_mem_of_isUnit_ev {T : Type} [CommRing T] (y : Sp T) {a : T} (h : IsUnit (ev y a)) :
    a ∉ (show PrimeSpectrum T from y).asIdeal := by
  rw [ev_eq, isUnit_gs_iff (𝟙 _) y (U := ⊤) trivial] at h
  have h' : y ∈ (Spec (CommRingCat.of T)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv a) := h
  rw [basicOpen_eq_of_affine] at h'
  exact h'

theorem span_eq_top (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  let y : Sp T := (⟨m, hm.isPrime⟩ : PrimeSpectrum T)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hk' : x y ∈ M.U k := X.basicOpen_le _ hk
  obtain ⟨u, hu⟩ := loc_of_secCoord h y k hk'
  have := (isUnit_gs_iff x y hk' _).2 hk
  rw [hu] at this
  exact not_mem_of_isUnit_ev y (isUnit_of_mul_isUnit_left this) (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem mem_of_X_mul_mem (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {F : MvPolynomial σ R}
    (hF : ∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) : F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  obtain ⟨s, c, e⟩ := GlobalTheory.SegreCoord.exists_comb (span_eq_top hc h)
  rw [← _root_.one_mul (MvPolynomial.eval₂ β v F), ← e, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := mem_idealOf.1 (hF i) T β x v hx h
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at this
  rw [_root_.mul_assoc, this, mul_zero]

variable (p th) in

def formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) : (lbPow M d).Sec where
  f j := MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
    (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F
  compat j j' := by
    have l₁ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j ⟨⟩) := inf_le_left.trans (Cartier.lbPow_U M d j).le
    have l₂ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j' ⟨⟩) := inf_le_right.trans (Cartier.lbPow_U M d j').le
    have e := fun i => Cartier.sec_compat (th i) (j ⟨⟩) (j' ⟨⟩) l₁ l₂
    change resG X _ _ = _ * resG X _ _
    refine (MvPolynomial.eval₂_comp_left _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      ((congrArg Units.val (Cartier.lbPow_g M d j j')).trans (Units.val_pow_eq_pow_val _ _))
      (MvPolynomial.eval₂_comp_left _ _ _ _)).symm)
    refine Eq.trans ?_ (eval₂_scale _ _ _ hF)
    congr 1
    · exact RingHom.ext fun a => (Cartier.resG_resG _ _ _).trans (Cartier.resG_resG _ _ _).symm
    · funext i
      exact (Cartier.resG_resG _ _ _).trans ((e i).trans (congrArg _ (Cartier.resG_resG _ _ _).symm))

theorem gs_formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) {T : Type} [CommRing T] {β : R →+* T}
    {x : Sp T ⟶ X} {v : σ → T} (hx : x ≫ p = spMap β) (h : SecCoord M th x v) (y : Sp T) (j : PUnit → M.ι)
    (hy : x y ∈ (lbPow M d).U j) : ∃ u : ((Sp T).presheaf.stalk y)ˣ,
      gs x y _ ((formSec p th hF).f j) = u * ev y (MvPolynomial.eval₂ β v F) := by
  obtain ⟨u, hu⟩ := loc_of_secCoord h y (j ⟨⟩) ((Cartier.lbPow_U M d j).le hy)
  refine ⟨u ^ d, ?_⟩
  let ψ : Γ(X, (lbPow M d).U j) →+* (Sp T).presheaf.stalk y :=
    ((Sp T).presheaf.germ (x ⁻¹ᵁ (lbPow M d).U j) y hy).hom.comp (x.app _).hom
  have hψ : ∀ a, gs x y _ a = ψ a := fun a => gs_eq x y _ hy a
  rw [hψ, MvPolynomial.eval₂_comp_left (ev y), Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
  refine (MvPolynomial.eval₂_comp_left ψ _ _ _).trans ?_
  congr 1
  · refine RingHom.ext fun a => ?_
    refine (hψ _).symm.trans ((gs_res x y le_top hy _).trans ((gs_pull x p y ⊤ trivial _).trans ?_))
    rw [hx, ← Category.comp_id (spMap β), GlobalTheory.SegreCoord.gs_stalkMap _ _ _ ⊤ trivial, ← ev_eq, ← ev_stalkMap]
    rfl
  · funext i
    exact (hψ _).symm.trans ((gs_res x y _ hy _).trans ((hu i).trans (_root_.mul_comm _ _)))

theorem formSec_eq_zero_iff (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) :
    (∀ j, (formSec p th hF).f j = 0) ↔ F ∈ idealOf p M th (𝟙 X) := by
  constructor
  · intro h0
    refine mem_idealOf.2 fun T _ β x v hx h => ev_ext fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hy : x y ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hx h y _ hy
    have h1 : gs x y _ (0 : Γ(X, (lbPow M d).U (fun _ => k))) = 0 := by rw [gs_eq x y _ hy, map_zero, map_zero]
    rw [map_zero]
    exact u.mul_right_eq_zero.1 (hu.symm.trans ((congrArg (gs x y _) (h0 fun _ => k)).trans h1))
  · intro hI j
    refine fn_ext fun z hz => ?_
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    let x : Sp Γ(X, V) ⟶ X := hV.fromSpec
    haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hV.fromSpec)
    have hr : Set.range x = V := hV.range_fromSpec
    obtain ⟨y, rfl⟩ : z ∈ Set.range x := hr.ge hzV
    obtain ⟨v, hv⟩ := exists_secCoord (th := th) hM (x := x) (k := j ⟨⟩)
      fun y => (Cartier.lbPow_U M d j).le (hle (hr.le ⟨y, rfl⟩))
    have hx : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := (Spec.map_preimage _).symm
    obtain ⟨u, hu⟩ := gs_formSec hF hx hv y j hz
    rw [mem_idealOf.1 hI _ _ x v hx hv, map_zero, mul_zero, ← Category.comp_id x,
      GlobalTheory.SegreCoord.gs_stalkMap x (𝟙 X) y _ hz] at hu
    rw [gs_eq (𝟙 X) (x y) _ hz 0, map_zero, map_zero]
    exact (asIso (x.stalkMap y)).commRingCatIsoToRingEquiv.injective (hu.trans (map_zero _).symm)

theorem eval_eq_zero_iff {K : Type} [Field K] {p : X ⟶ Sp K} (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) {y : Sp K ⟶ X} {v : σ → K} (hy : y ≫ p = 𝟙 _) (h : SecCoord M th y v) :
    MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (formSec p th hF) := by
  have hy' : y ≫ p = spMap (RingHom.id K) := hy.trans (Spec.map_id (CommRingCat.of K)).symm
  rw [← not_iff_not, not_not]
  constructor
  · intro h0 z _
    obtain ⟨k, hk⟩ := exists_chart hM (y z)
    have hz : y z ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z _ hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, (isUnit_gs_iff y z hz _).1 ?_⟩
    rw [hu]
    exact u.isUnit.mul ((Ne.isUnit h0).map (ev z))
  · intro hle h0
    let z : Sp K := (⊥ : PrimeSpectrum K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y z ∈ Out.nonzeroLocus (formSec p th hF) from hle (Set.mem_univ z))
    have hz : y z ∈ (lbPow M d).U j := X.basicOpen_le _ hj
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z j hz
    have hun := (isUnit_gs_iff y z hz _).2 hj
    rw [hu, show MvPolynomial.eval₂ (RingHom.id K) v F = 0 from h0, map_zero, mul_zero] at hun
    exact not_isUnit_zero hun

theorem ideal_of_veryAmple : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) :=
  fun _ _ _ _ _ p _ th hM hV => ⟨fun _ hF e => homogeneousComponent_mem hF e, fun _ hF => mem_of_X_mul_mem hV.1 hF,
    fun _ _ hF => ⟨formSec p th hF, fun _ => rfl, formSec_eq_zero_iff hM hF,
      fun _ _ hy h => eval_eq_zero_iff hM hF hy h⟩⟩

end GlobalTheory.ZV.FormSec
end
